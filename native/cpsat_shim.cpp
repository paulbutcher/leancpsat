// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

// The whole shim: hand serialized CpModelProto/SatParameters bytes to CP-SAT
// and hand serialized CpSolverResponse bytes back. Model structure never
// crosses this boundary, only bytes, so this file does not grow as
// Cpsat.Model/Cpsat.Proto gain more constraint kinds.
//
// `cpsat_solve`/`cpsat_solve_interruptible` go through CP-SAT's own trimmed C
// API (`cp_solver_c.h`), a thin wrapper around a single blocking call to the
// C++ `SolveCpModel(CpModelProto, Model*)` entry point. The streaming solve
// (`cpsat_solve_stream_*`) calls that same C++ entry point directly, since
// only it exposes `NewFeasibleSolutionObserver`, which `cp_solver_c.h`
// doesn't wrap.

#include <atomic>
#include <condition_variable>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <utility>

#include <lean/lean.h>

#include "ortools/sat/c_api/cp_solver_c.h"
#include "ortools/sat/cp_model.pb.h"
#include "ortools/sat/cp_model_solver.h"
#include "ortools/sat/model.h"
#include "ortools/sat/sat_parameters.pb.h"
#include "ortools/sat/util.h"

// libstdc++'s <memory>/<thread> headers, when compiled against glibc >= 2.32
// headers (as this file is, via the system compiler), read this glibc-provided
// flag to skip atomic refcounting on the fast path when single-threaded.
// Lean's own bundled glibc predates 2.32 and doesn't export it, so this file
// provides it directly rather than pulling in an incompatible newer glibc
// alongside Lean's own; 0 ("might be multi-threaded", glibc's own default
// value before any thread is spawned) is always safe, just never elides the
// atomic op.
extern "C" { char __libc_single_threaded = 0; }

namespace {

using operations_research::sat::CpModelProto;
using operations_research::sat::CpSolverResponse;
using operations_research::sat::Model;
using operations_research::sat::ModelSharedTimeLimit;
using operations_research::sat::NewFeasibleSolutionObserver;
using operations_research::sat::NewSatParameters;
using operations_research::sat::SatParameters;
using operations_research::sat::SolveCpModel;

void cpsat_external_foreach(void *, b_lean_obj_arg) {}

lean_obj_res cpsat_bytes_of(const void *data, int len) {
  lean_obj_res arr = lean_alloc_sarray(1, static_cast<size_t>(len),
                                       static_cast<size_t>(len));
  if (len > 0) {
    std::memcpy(lean_sarray_cptr(arr), data, static_cast<size_t>(len));
  }
  return arr;
}

// Wraps the `CpSatEnv*` the trimmed C API (`cp_solver_c.h`) hands out for
// `cpsat_solve_interruptible`, unchanged, plus a second stop path a
// streaming solve can register itself with: `cp_solver_c.h` has no way to
// reach the `Model` inside its opaque env, so a streaming solve builds its
// own `Model`/`ModelSharedTimeLimit` directly against the advanced C++ API
// instead of going through it. Both paths share one `stopped`/`mu`, so a
// single Lean `StopToken` can cancel whichever kind of solve is using it.
struct LeanStopToken {
  void *legacy_cenv;
  std::mutex mu;
  bool stopped = false;
  ModelSharedTimeLimit *active_stream_limit = nullptr;
};

void cpsat_stop_token_finalize(void *data) {
  auto *t = static_cast<LeanStopToken *>(data);
  SolveCpDestroyEnv(t->legacy_cenv);
  delete t;
}

lean_external_class *cpsat_stop_token_class() {
  static lean_external_class *cls =
      lean_register_external_class(cpsat_stop_token_finalize,
                                    cpsat_external_foreach);
  return cls;
}

struct StreamUpdate {
  bool is_done;
  std::string bytes;
};

struct StreamState {
  std::mutex mu;
  std::condition_variable cv;
  std::deque<StreamUpdate> queue;
  std::atomic<bool> finished{false};
};

// Owns the background solve thread. `token` is an owned reference (acquired
// in `cpsat_solve_stream_start`, released here) so the `LeanStopToken` the
// worker thread reads/writes stays alive for as long as the worker might
// still be running, regardless of what the Lean-visible `StopToken` value
// itself does in the meantime.
struct StreamHandle {
  std::thread worker;
  std::shared_ptr<StreamState> state;
  lean_object *token;
};

void cpsat_stream_handle_finalize(void *data) {
  auto *h = static_cast<StreamHandle *>(data);
  if (!h->state->finished.load()) {
    // The handle is being dropped before the search finished on its own
    // (e.g. the caller only wanted the first solution): force it to wind
    // down instead of leaking the thread or letting it run to completion
    // unobserved.
    auto *t = static_cast<LeanStopToken *>(lean_get_external_data(h->token));
    std::lock_guard<std::mutex> lock(t->mu);
    t->stopped = true;
    if (t->active_stream_limit != nullptr) {
      t->active_stream_limit->Stop();
    }
  }
  h->worker.join();
  lean_dec_ref(h->token);
  delete h;
}

lean_external_class *cpsat_stream_handle_class() {
  static lean_external_class *cls =
      lean_register_external_class(cpsat_stream_handle_finalize,
                                    cpsat_external_foreach);
  return cls;
}

// Runs on a background thread the shim itself spawns, never on a thread
// OR-Tools creates: CP-SAT's own solution-observer callback (registered
// below) can fire from any of CP-SAT's internal worker threads, none of
// which are safe to run Lean code on. So this whole function, including the
// callback, only ever touches plain C++ (protobuf messages, the
// mutex-guarded queue), and hands finished byte strings off to
// `cpsat_solve_stream_next`, which runs on the Lean-registered calling
// thread and is the only place any `lean_object` gets built from them.
void RunStream(std::string model_bytes, std::string params_bytes,
               LeanStopToken *token, std::shared_ptr<StreamState> state) {
  CpModelProto req;
  req.ParseFromArray(model_bytes.data(), static_cast<int>(model_bytes.size()));
  SatParameters params;
  params.ParseFromArray(params_bytes.data(),
                        static_cast<int>(params_bytes.size()));

  Model model;
  ModelSharedTimeLimit *shared_time_limit =
      model.GetOrCreate<ModelSharedTimeLimit>();
  {
    std::lock_guard<std::mutex> lock(token->mu);
    token->active_stream_limit = shared_time_limit;
    if (token->stopped) {
      shared_time_limit->Stop();
    }
  }

  model.Add(NewSatParameters(params));
  model.Add(NewFeasibleSolutionObserver(
      [state](const CpSolverResponse &response) {
        std::string bytes;
        response.SerializeToString(&bytes);
        {
          std::lock_guard<std::mutex> lock(state->mu);
          state->queue.push_back({false, std::move(bytes)});
        }
        state->cv.notify_one();
      }));

  CpSolverResponse final_response = SolveCpModel(req, &model);

  // Unregister before `model` (and `shared_time_limit` with it) goes out of
  // scope below, so `cpsat_stop_token_stop`/the finalizer above never call
  // `Stop()` on a pointer that's about to be dangling.
  {
    std::lock_guard<std::mutex> lock(token->mu);
    token->active_stream_limit = nullptr;
  }

  std::string final_bytes;
  final_response.SerializeToString(&final_bytes);
  {
    std::lock_guard<std::mutex> lock(state->mu);
    state->queue.push_back({true, std::move(final_bytes)});
    state->finished.store(true);
  }
  state->cv.notify_one();
}

}  // namespace

extern "C" {

// The response buffer is allocated by OR-Tools via `strings::memdup`, i.e.
// plain `malloc`; ownership passes to us, so we must `free` it after copying.
LEAN_EXPORT lean_obj_res cpsat_solve(b_lean_obj_arg model_bytes,
                                     b_lean_obj_arg params_bytes,
                                     lean_obj_arg /* w */) {
  void *cres = nullptr;
  int cres_len = 0;
  SolveCpModelWithParameters(
      lean_sarray_cptr(model_bytes), static_cast<int>(lean_sarray_size(model_bytes)),
      lean_sarray_cptr(params_bytes), static_cast<int>(lean_sarray_size(params_bytes)),
      &cres, &cres_len);
  lean_obj_res result = cpsat_bytes_of(cres, cres_len);
  std::free(cres);
  return lean_io_result_mk_ok(result);
}

LEAN_EXPORT lean_obj_res cpsat_new_stop_token(lean_obj_arg /* w */) {
  auto *t = new LeanStopToken();
  t->legacy_cenv = SolveCpNewEnv();
  return lean_io_result_mk_ok(lean_alloc_external(cpsat_stop_token_class(), t));
}

LEAN_EXPORT lean_obj_res cpsat_stop_token_stop(b_lean_obj_arg token,
                                               lean_obj_arg /* w */) {
  auto *t = static_cast<LeanStopToken *>(lean_get_external_data(token));
  SolveCpStopSearch(t->legacy_cenv);
  std::lock_guard<std::mutex> lock(t->mu);
  t->stopped = true;
  if (t->active_stream_limit != nullptr) {
    t->active_stream_limit->Stop();
  }
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res cpsat_solve_interruptible(b_lean_obj_arg token,
                                                    b_lean_obj_arg model_bytes,
                                                    b_lean_obj_arg params_bytes,
                                                    lean_obj_arg /* w */) {
  auto *t = static_cast<LeanStopToken *>(lean_get_external_data(token));
  void *cres = nullptr;
  int cres_len = 0;
  SolveCpInterruptible(
      t->legacy_cenv,
      lean_sarray_cptr(model_bytes), static_cast<int>(lean_sarray_size(model_bytes)),
      lean_sarray_cptr(params_bytes), static_cast<int>(lean_sarray_size(params_bytes)),
      &cres, &cres_len);
  lean_obj_res result = cpsat_bytes_of(cres, cres_len);
  std::free(cres);
  return lean_io_result_mk_ok(result);
}

// Copies the model/params bytes onto the C++ heap and starts the background
// solve thread; returns immediately with a handle to pull updates from via
// `cpsat_solve_stream_next`. `token` is borrowed by this call but its
// underlying `LeanStopToken` is kept alive (via an owned reference on the
// returned handle) for as long as the background thread might still touch
// it, released only once that thread has been joined.
LEAN_EXPORT lean_obj_res cpsat_solve_stream_start(b_lean_obj_arg token,
                                                  b_lean_obj_arg model_bytes,
                                                  b_lean_obj_arg params_bytes,
                                                  lean_obj_arg /* w */) {
  std::string model_str(reinterpret_cast<const char *>(lean_sarray_cptr(model_bytes)),
                        lean_sarray_size(model_bytes));
  std::string params_str(reinterpret_cast<const char *>(lean_sarray_cptr(params_bytes)),
                         lean_sarray_size(params_bytes));

  auto *h = new StreamHandle();
  h->state = std::make_shared<StreamState>();
  h->token = token;
  lean_inc_ref(token);

  auto *token_data = static_cast<LeanStopToken *>(lean_get_external_data(token));
  auto state = h->state;
  h->worker = std::thread(
      [token_data, state, model_str = std::move(model_str),
       params_str = std::move(params_str)]() mutable {
        RunStream(std::move(model_str), std::move(params_str), token_data, state);
      });

  return lean_io_result_mk_ok(lean_alloc_external(cpsat_stream_handle_class(), h));
}

// Blocks until the next update is available and returns it as `(isDone,
// responseBytes)`. Errors if called again after an update with `isDone =
// true` has already been returned once.
LEAN_EXPORT lean_obj_res cpsat_solve_stream_next(b_lean_obj_arg handle,
                                                 lean_obj_arg /* w */) {
  auto *h = static_cast<StreamHandle *>(lean_get_external_data(handle));
  std::unique_lock<std::mutex> lock(h->state->mu);
  while (h->state->queue.empty()) {
    if (h->state->finished.load()) {
      return lean_io_result_mk_error(lean_mk_io_user_error(
          lean_mk_string("Cpsat: solution stream already finished")));
    }
    h->state->cv.wait(lock);
  }
  StreamUpdate update = std::move(h->state->queue.front());
  h->state->queue.pop_front();
  lock.unlock();

  lean_obj_res bytes_obj =
      cpsat_bytes_of(update.bytes.data(), static_cast<int>(update.bytes.size()));
  lean_obj_res pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, lean_box(update.is_done ? 1 : 0));
  lean_ctor_set(pair, 1, bytes_obj);
  return lean_io_result_mk_ok(pair);
}

}  // extern "C"
