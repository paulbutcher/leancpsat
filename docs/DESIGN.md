<!-- Copyright (c) 2026 Paul Butcher. All rights reserved.
     Released under Apache 2.0 license as described in the file LICENSE. -->

# Design: Lean bindings for CP-SAT

Scope: expose OR-Tools' CP-SAT constraint solver (only CP-SAT, not linear/MIP solvers,
routing, graph algorithms, etc.) to Lean programs, backed by the prebuilt OR-Tools C++
distributions checked into `or-tools/`.

## 1. The FFI boundary

OR-Tools ships `include/ortools/sat/c_api/cp_solver_c.h` in both prebuilt SDKs:

```c
void SolveCpModelWithParameters(const void* creq, int creq_len,
                                const void* cparams, int cparams_len,
                                void** cres, int* cres_len);

void* SolveCpNewAtomicBool();
void SolveCpDestroyAtomicBool(void* atomic_bool);
void SolveCpStopSolve(void* atomic_bool);
void SolveCpInterruptible(void* limit_reached, const void* creq, int creq_len,
                          const void* cparams, int cparams_len, void** cres,
                          int* cres_len);
```

`creq`/`cparams` are serialized `CpModelProto`/`SatParameters` messages; `cres` comes back
as a serialized `CpSolverResponse`. This is the same boundary OR-Tools' own non-C++
language bindings (Go, etc.) cross via cgo/JNI: build a proto, serialize it, hand bytes
across, get bytes back.

This changes the whole shape of the binding:

- **We do not need to wrap `CpModelBuilder`, `IntVar`, `LinearExpr`, `Constraint`, `Domain`,
  ... in hand-written C++ shims with lifetime management across the FFI boundary.** That
  would mean dozens of exported functions and object-handle bookkeeping (every C++ object
  needs a Lean-side external handle with a finalizer).
- **The only FFI surface we own is "bytes in, bytes out" plus a tiny cancellation
  token.** Everything else - building the model, reading the result - is plain,
  ordinary, GC'd Lean code operating on Lean data structures.
- We do need a protobuf encoder for `CpModelProto`/`SatParameters` and a decoder for
  `CpSolverResponse`. Rather than hand-writing the wire-format primitives (varint, tag,
  length-delimited submessage, packed-repeated encoding), we use
  [Lean-zh/protobuf](https://github.com/Lean-zh/protobuf) in its "manual message
  definition" mode: declare the message shapes for the specific fields we need using its
  internal notation, and get its already-implemented (and unit-tested) wire codec
  underneath - including edge cases like varint two's-complement encoding of negative
  values and packed-vs-expanded repeated fields that a hand-rolled version would have to
  get right from scratch. Crucially, this mode does **not** need `protoc` or the actual
  `.proto` sources (which aren't vendored in `or-tools/` - only the generated `.pb.h`
  headers are); the library's other three usage modes (`#load_proto_file`,
  `#load_proto_dir`, its protoc plugin) all shell out to an installed `protoc` binary and
  are deliberately not used here, since installing `protoc` is exactly the kind of
  OS-level build dependency this project avoids. Field numbers for the message shapes we
  declare still come straight from the vendored generated headers
  (`kVarsFieldNumber`, `kConstraintsFieldNumber`, ... in `cp_model.pb.h`), so there's a
  single source of truth: what's physically checked into `or-tools/`.

```
┌─────────────────────────────────────────────────────────────┐
│ Lean: Cpsat.Model        - pure builder API (IntVar, BoolVar,│
│                            LinearExpr, Constraint, CpModelM) │
├─────────────────────────────────────────────────────────────┤
│ Lean: Cpsat.Proto        - message decls on Lean-zh/protobuf: │
│                            CpModel/SatParameters -> ByteArray│
│                            ByteArray -> CpSolverResponse     │
├─────────────────────────────────────────────────────────────┤
│ Lean: Cpsat.Solver       - @[extern] decls + solve/solveWith │
├─────────────────────────────────────────────────────────────┤
│ C++ shim: native/cpsat_shim.cpp - ByteArray <-> void*/len,   │
│                            calls into cp_solver_c.h          │
├─────────────────────────────────────────────────────────────┤
│ OR-Tools: libortools.{so,dylib} (prebuilt, in or-tools/*/lib)│
└─────────────────────────────────────────────────────────────┘
```

Everything above the shim is pure Lean and platform-independent; only the shim and the
lakefile's link flags are platform-specific.

## 2. Lean public API

Naming mirrors the C++ `CpModelBuilder` API (`cp_model.h`) where practical, since that's
the API surface most CP-SAT users already know.

```lean
namespace Cpsat

structure Domain where
  intervals : Array (Int64 × Int64)  -- inclusive, sorted, disjoint

def Domain.fromInterval (lo hi : Int64) : Domain := ...
def Domain.singleton (v : Int64) : Domain := ...

structure BoolVar where private mk :: (index : Nat)
structure IntVar  where private mk :: (index : Nat)

-- affine combination of int/bool vars plus a constant
structure LinearExpr where
  terms    : Array (IntVar × Int64)
  constant : Int64

instance : Add LinearExpr := ...
instance : HMul Int64 IntVar LinearExpr := ...
instance : Coe IntVar LinearExpr := ...
instance : Coe BoolVar LinearExpr := ...   -- 0/1

structure Constraint where private mk :: (index : Nat)

-- model-building is a plain state monad over the in-progress model; no FFI involved here
abbrev CpModelM := StateM CpModel.State

def newBoolVar (name : String := "") : CpModelM BoolVar
def newIntVar (domain : Domain) (name : String := "") : CpModelM IntVar
def newConstant (value : Int64) : CpModelM IntVar

def addLinearConstraint (expr : LinearExpr) (domain : Domain) : CpModelM Constraint
def addEquality        (lhs rhs : LinearExpr) : CpModelM Constraint
def addLessOrEqual     (lhs rhs : LinearExpr) : CpModelM Constraint
def addGreaterOrEqual  (lhs rhs : LinearExpr) : CpModelM Constraint
def addNotEqual        (lhs rhs : LinearExpr) : CpModelM Constraint
def addAllDifferent    (vars : Array IntVar)  : CpModelM Constraint

def addBoolOr      (lits : Array BoolVar) : CpModelM Constraint
def addBoolAnd     (lits : Array BoolVar) : CpModelM Constraint
def addAtMostOne    (lits : Array BoolVar) : CpModelM Constraint
def addExactlyOne   (lits : Array BoolVar) : CpModelM Constraint
def addImplication  (a b : BoolVar)         : CpModelM Constraint

def Constraint.onlyEnforceIf (c : Constraint) (lits : Array BoolVar) : CpModelM Unit

def minimize (expr : LinearExpr) : CpModelM Unit
def maximize (expr : LinearExpr) : CpModelM Unit

structure SolverParameters where
  maxTimeInSeconds  : Option Float := none
  numWorkers        : Option Nat   := none
  randomSeed        : Option Nat   := none
  logSearchProgress : Bool         := false

inductive CpSolverStatus | unknown | modelInvalid | feasible | infeasible | optimal
  deriving Repr, DecidableEq

structure CpSolverResponse where
  status            : CpSolverStatus
  objectiveValue    : Float
  bestObjectiveBound : Float
  solution          : Array Int64   -- indexed by IntVar.index
  wallTime          : Float

def CpSolverResponse.value (r : CpSolverResponse) (v : IntVar) : Int64 :=
  r.solution.getD v.index 0

-- entry point: run a model-building computation, then solve it.
def solve (params : SolverParameters := {}) (m : CpModelM α) : IO (α × CpSolverResponse)

-- cooperative cancellation, e.g. from another Lean task/thread
opaque StopToken.Pointed : NonemptyType
def StopToken := StopToken.Pointed.type
instance : Nonempty StopToken := StopToken.Pointed.property

def StopToken.new : IO StopToken
def StopToken.stop (t : StopToken) : IO Unit

def solveInterruptible (params : SolverParameters) (token : StopToken)
    (m : CpModelM α) : IO (α × CpSolverResponse)

end Cpsat
```

Example (the canonical "rabbits and pheasants" CP-SAT sample):

```lean
open Cpsat in
def rabbitsAndPheasants : IO Unit := do
  let (⟨rabbits, pheasants⟩, resp) ← solve (m := do
    let rabbits   ← newIntVar (.fromInterval 0 20) "rabbits"
    let pheasants ← newIntVar (.fromInterval 0 20) "pheasants"
    let _ ← addEquality (rabbits + pheasants) (LinearExpr.const 20)
    let _ ← addEquality (4 * rabbits + 2 * pheasants) (LinearExpr.const 56)
    pure (rabbits, pheasants))
  match resp.status with
  | .optimal | .feasible =>
    IO.println s!"rabbits = {resp.value rabbits}, pheasants = {resp.value pheasants}"
  | _ => IO.println "no solution"
```

Only a **subset** of CP-SAT's constraint kinds is proposed for v1 (linear constraints,
`AllDifferent`, boolean logic, a single linear objective) - enough for a large class of
real models. Because the FFI boundary is just bytes, adding more constraint kinds later
(intervals/`NoOverlap`/`Cumulative`, `Element`, `Table`, `Circuit`, ...) is purely a matter
of extending `Cpsat.Proto` with more message declarations; it never touches the C++ shim
or the lakefile. This scales particularly well under Lean-zh/protobuf: `ConstraintProto`
in the real schema is itself one large `oneof` over roughly thirty constraint kinds, so
broader coverage needs correct `oneof` handling regardless of codec strategy - the
library already provides that, whereas a hand-rolled codec would have to grow its own
oneof-dispatch logic as more kinds are added, with a fresh chance of a wire-level mistake
in each new message shape. Growing feature coverage is then mostly new field
declarations plus new `CpModelM` builder functions, not new wire-format code.

## 3. Wire format layer (`Cpsat.Proto`)

Depends on [`Lean-zh/protobuf`](https://github.com/Lean-zh/protobuf) (MIT licensed) as a
Lake dependency, used exclusively in its **manual message definition** mode (no `protoc`,
no `.proto` sources needed):

```lean
require protobuf from git
  "https://github.com/Lean-zh/protobuf.git" @ "<pinned-commit-sha>"
```

Pinned to a commit SHA rather than a version tag, since the upstream repo has no tagged
releases at time of writing. Its `lean-toolchain` (`v4.32.0`) is a patch version behind
this project's (`v4.32.2`); confirming the two build together is the first implementation
step (see §7).

`Cpsat.Proto` declares, by hand, just the message shapes our supported feature subset
touches - using the library's notation, not a `.proto` file - with field numbers read
directly off the vendored generated headers (no proto source needed), e.g. from
`cp_model.pb.h`: `IntegerVariableProto.kDomainFieldNumber = 2`,
`CpModelProto.kVariablesFieldNumber`, `CpModelProto.kConstraintsFieldNumber = 3`,
`CpModelProto.kObjectiveFieldNumber = 4`; and from `CpSolverResponse`:
`kStatusFieldNumber = 1`, `kSolutionFieldNumber = 2`, `kObjectiveValueFieldNumber = 3`,
`kBestObjectiveBoundFieldNumber = 4`, `kWallTimeFieldNumber = 15`. `SatParameters` fields
used: `kMaxTimeInSecondsFieldNumber = 36`, `kNumWorkersFieldNumber = 206`,
`kRandomSeedFieldNumber = 31`, `kLogSearchProgressFieldNumber = 41`.

Each declared message gets, for free from the library: correct varint/length-delimited/
fixed64 encoding, packed repeated fields, and unknown-field preservation (so the decoder
degrades gracefully as OR-Tools adds new `CpSolverResponse` fields in future versions).
`Cpsat.Proto` itself is then just: a small set of declarative message-shape declarations,
plus thin conversion functions between those generated Lean message types and the
friendly `Cpsat.Model` types (`IntVar`/`BoolVar`/`LinearExpr`/... to/from
`IntegerVariableProto`/`ConstraintProto`/...). No hand-written wire-format code, no
`unsafe`, no manual byte-buffer manipulation.

This module still gets a solid round-trip test (build a model with the Lean builder,
encode it, decode a hand-built `CpSolverResponse` byte string, check field extraction) -
that's now testing our field mappings, not bit-level encoding logic, since the latter is
the upstream library's responsibility.

## 4. C++ shim (`native/cpsat_shim.cpp`)

Small and fixed in size regardless of how many constraint kinds the Lean side later
supports, since it never sees model structure - only byte buffers:

```cpp
extern "C" {

// model_bytes, params_bytes borrowed; returns a fresh Lean ByteArray (CpSolverResponse).
lean_object* cpsat_solve(b_lean_obj_arg model_bytes, b_lean_obj_arg params_bytes);

// cancellation token, wrapped as a Lean external object with a finalizer that calls
// SolveCpDestroyAtomicBool.
lean_object* cpsat_new_stop_token();
lean_object* cpsat_stop(b_lean_obj_arg token);

lean_object* cpsat_solve_interruptible(b_lean_obj_arg token,
                                        b_lean_obj_arg model_bytes,
                                        b_lean_obj_arg params_bytes);
}
```

`cpsat_solve` reads the `ByteArray`'s data pointer/size via Lean's C API
(`lean_sarray_cptr`/`lean_sarray_size`), calls `SolveCpModelWithParameters`, copies the
`cres`/`cres_len` buffer into a freshly allocated Lean `ByteArray`, and frees the buffer
OR-Tools allocated (per `cp_solver_c.h`'s ownership contract - needs confirming against
the header/implementation notes during implementation, since the header alone doesn't
state who frees `*cres`).

## 5. Lakefile design

Requirements from the prompt: build on both Linux and macOS; the user drops the matching
OR-Tools SDK under `or-tools/` themselves (already true here: `or-tools/or-tools_x86_64_
Ubuntu-24.10_cpp_v9.12.4544/` and `or-tools/or-tools_arm64_macOS-15.3.1_cpp_v9.12.4544/`).

The lakefile also needs a `require` for the `protobuf` Lake dependency (§3), fetched from
git and pinned to a commit SHA. This is a network dependency at first build (or a
manually-vendored one, if the user prefers not to have `lake build` reach the network) -
unlike the OR-Tools SDK itself, which is always local and never fetched by Lake.

Because SDK directory names are version- and platform-specific, the lakefile should not
hardcode either. Instead, at configure time:

1. List entries under `or-tools/`. Require exactly one directory that looks like an
   OR-Tools SDK (contains `include/ortools/sat/cp_model.h`); error out with a clear
   message ("no SDK found, download one for your platform and extract it under
   or-tools/" / "found N candidates, expected exactly one") otherwise. This makes the
   lakefile itself platform-agnostic - it doesn't need to know it's "Ubuntu" vs "macOS",
   only that whichever single SDK is present matches the host.
2. Derive `<sdk>/include` and `<sdk>/lib` from that directory.
3. Compile `native/cpsat_shim.cpp` as a C++ shim, with:
   - `-I <sdk>/include -I <lean include dir> -std=c++20` (OR-Tools 9.x requires C++20)
   - link against `-L <sdk>/lib -lortools`
   - an rpath so the built Lean binary/shared lib finds `libortools.{so,dylib}` at
     runtime without requiring `LD_LIBRARY_PATH`/`DYLD_LIBRARY_PATH`: `-Wl,-rpath,<sdk>/lib`
     works with both GNU ld (Linux) and macOS's linker.

Sketch (exact Lake API calls - `extern_lib`, `moreLeancArgs`, whether directory listing
needs `unsafe`/`IO` plumbing at config time - to be nailed down during implementation,
but the shape is):

```lean
import Lake
open Lake DSL System

def orToolsSdkDir (pkgDir : FilePath) : IO FilePath := do
  let base := pkgDir / "or-tools"
  let candidates ← (← base.readDir).filterM fun e =>
    (e.path / "include" / "ortools" / "sat" / "cp_model.h").pathExists
  match candidates with
  | #[e] => return e.path
  | #[]  => throw <| IO.userError
      s!"No OR-Tools SDK found under {base}. Download the release for this platform \
         and extract it there before building."
  | _    => throw <| IO.userError
      s!"Multiple OR-Tools SDKs found under {base}; expected exactly one."

package cpsat

extern_lib cpsatShim pkg := do
  let sdk ← orToolsSdkDir pkg.dir
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cpsat_shim.cpp"
  buildO (pkg.buildDir / "native" / "cpsat_shim.o") srcJob
    #["-I", (sdk / "include").toString, "-I", (← getLeanIncludeDir).toString,
      "-std=c++20", "-fPIC"]
  -- ... link into a static/shared lib, propagate -L/-l/-rpath to downstream targets
```

Consuming executables/tests get `moreLinkArgs := #["-L<sdk>/lib", "-lortools",
"-Wl,-rpath,<sdk>/lib"]` computed the same way.

## 6. Testing

- `Cpsat/Proto` gets round-trip tests for our message declarations and Model conversions
  (encode a tiny model, decode a hand-built `CpSolverResponse` byte string, check field
  extraction) - the wire-format logic itself is Lean-zh/protobuf's concern, tested there.
- An integration test (`lake test`) building the rabbits-and-pheasants model (or an
  equally small canonical example) end-to-end through `solve` and asserting the known
  optimal values - this is the real proof the FFI boundary and linking are correct.
- CI would need to run on both an Ubuntu and a macOS runner with the matching SDK
  present, since there's no way to cross-test the binary linking otherwise.

## 7. Open questions to resolve during implementation

- Buffer ownership for `cres`/`cres_len` out of `SolveCpModelWithParameters` (who frees
  it - confirm against OR-Tools source, not just the header).
- Exact current Lake DSL incantations for a dynamically-located external library
  (`extern_lib` vs `target` vs `input_dir`, and how directory-listing IO composes with
  Lake's config-time monad) - the sketch above captures intent, not verified syntax.
- Whether to vendor a fixed subset of `SatParameters`/`CpModelProto` field numbers as
  Lean constants with a comment citing the OR-Tools version they were read from, so a
  future OR-Tools upgrade that renumbers (unlikely - proto field numbers are effectively
  permanent) is at least detectable.
- **First implementation step**: confirm `Lean-zh/protobuf` (`lean-toolchain v4.32.0`)
  actually builds as a dependency of this package (`lean-toolchain v4.32.2`) before
  writing any code against it. If it doesn't, fall back to the hand-rolled wire-codec
  design (varint/tag/length-delimited primitives written directly in `Cpsat.Proto`).
- Pin `protobuf`'s `require` to a specific commit SHA (no tagged releases exist upstream)
  and record which SHA was validated, since there's no version number to reason about
  compatibility from.
