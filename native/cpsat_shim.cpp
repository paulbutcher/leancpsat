// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.

// The whole shim: hand serialized CpModelProto/SatParameters bytes to CP-SAT's
// own C API and hand the serialized CpSolverResponse bytes back. Model
// structure never crosses this boundary, only bytes, so this file does not
// grow as Cpsat.Model/Cpsat.Proto gain more constraint kinds.

#include <cstdlib>
#include <cstring>

#include <lean/lean.h>

#include "ortools/sat/c_api/cp_solver_c.h"

namespace {

void cpsat_stop_token_finalize(void *data) {
  SolveCpDestroyAtomicBool(data);
}

void cpsat_stop_token_foreach(void *, b_lean_obj_arg) {}

lean_external_class *cpsat_stop_token_class() {
  static lean_external_class *cls =
      lean_register_external_class(cpsat_stop_token_finalize,
                                    cpsat_stop_token_foreach);
  return cls;
}

lean_obj_res cpsat_bytes_of(const void *data, int len) {
  lean_obj_res arr = lean_alloc_sarray(1, static_cast<size_t>(len),
                                       static_cast<size_t>(len));
  if (len > 0) {
    std::memcpy(lean_sarray_cptr(arr), data, static_cast<size_t>(len));
  }
  return arr;
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
  void *token = SolveCpNewAtomicBool();
  return lean_io_result_mk_ok(lean_alloc_external(cpsat_stop_token_class(), token));
}

LEAN_EXPORT lean_obj_res cpsat_stop_token_stop(b_lean_obj_arg token,
                                               lean_obj_arg /* w */) {
  SolveCpStopSolve(lean_get_external_data(token));
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res cpsat_solve_interruptible(b_lean_obj_arg token,
                                                    b_lean_obj_arg model_bytes,
                                                    b_lean_obj_arg params_bytes,
                                                    lean_obj_arg /* w */) {
  void *cres = nullptr;
  int cres_len = 0;
  SolveCpInterruptible(
      lean_get_external_data(token),
      lean_sarray_cptr(model_bytes), static_cast<int>(lean_sarray_size(model_bytes)),
      lean_sarray_cptr(params_bytes), static_cast<int>(lean_sarray_size(params_bytes)),
      &cres, &cres_len);
  lean_obj_res result = cpsat_bytes_of(cres, cres_len);
  std::free(cres);
  return lean_io_result_mk_ok(result);
}

}  // extern "C"
