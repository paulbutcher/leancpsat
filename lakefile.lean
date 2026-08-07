-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Lake
open Lake DSL System

/-- Run a command with inherited stdio (so its output streams live), throwing
if it exits non-zero. -/
def runStreaming (cmd : String) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args }
  let exitCode ← child.wait
  unless exitCode == 0 do
    throw <| IO.userError s!"`{cmd} {" ".intercalate args.toList}` exited with code {exitCode}"

/-- Build OR-Tools from the vendored source checkout via CMake, essentially
the two commands recorded in `notes.txt`. This only runs once: subsequent
`findOrToolsBuild` calls see `libortools.{so,dylib}` already present and skip
it.

Builds in parallel via a bare `-j` (cmake's own heuristic, generally the
number of hardware threads) since that's fast on most machines. On a
memory-constrained machine that heuristic can OOM (more parallel C++
translation units than there's RAM for), so `LEANCPSAT_ORTOOLS_JOBS`
overrides it with an explicit job count. -/
def buildOrTools (orToolsDir buildDir : FilePath) : IO Unit := do
  IO.println s!"{buildDir}/lib/{nameToSharedLib "ortools"} not found; building OR-Tools from \
    source. This is a one-time step and can take a long time."
  runStreaming "cmake" #["-S", orToolsDir.toString, "-B", buildDir.toString,
    "-DBUILD_DEPS=ON", "-DBUILD_FLATZINC=OFF", "-DBUILD_TESTING=OFF",
    "-DBUILD_SAMPLES=OFF", "-DBUILD_EXAMPLES=OFF"]
  let jobsArg ←
    match ← IO.getEnv "LEANCPSAT_ORTOOLS_JOBS" with
    | some jobs => pure s!"-j{jobs}"
    | none => pure "-j"
  runStreaming "cmake"
    #["--build", buildDir.toString, "--config", "Release", "--target", "all", "-v", jobsArg]

/--
Locate the OR-Tools checkout under `or-tools/` and its CMake build tree,
building it first if necessary. `or-tools/` is a full source checkout (not a
downloaded prebuilt SDK), so headers live at `or-tools/ortools/...` and the
built shared libraries live at `or-tools/build/lib`.
-/
def findOrToolsBuild (orToolsDir : FilePath) : IO FilePath := do
  let header := orToolsDir / "ortools" / "sat" / "cp_model.h"
  unless (← header.pathExists) do
    throw <| IO.userError s!"{header} not found. Expected a full OR-Tools source checkout under {orToolsDir}."
  let buildDir := orToolsDir / "build"
  let lib := buildDir / "lib" / nameToSharedLib "ortools"
  unless (← lib.pathExists) do
    buildOrTools orToolsDir buildDir
    unless (← lib.pathExists) do
      throw <| IO.userError
        s!"{lib} still missing after building OR-Tools; check the build output above for errors."
  return buildDir

-- `orToolsDir` and `orToolsBuild / "lib"` are treated as a stable interface: consumers
-- that `require` this package (see the README's "Using cpsat as a dependency") must
-- reconstruct these same paths themselves, since Lake does not propagate
-- `weakLeancArgs`/`weakLinkArgs` across a `require`. Keep the README's snippet in sync
-- with any change here.
def orToolsDir : FilePath := __dir__ / "or-tools"
def orToolsBuild : FilePath := run_io findOrToolsBuild orToolsDir
def orToolsInclude : FilePath := orToolsDir
def orToolsLib : FilePath := orToolsBuild / "lib"

package cpsat where
  version := v!"0.1.0"
  -- Weak: these embed a local, machine-specific path, so they must not affect
  -- build artifact hashes (see Lake's `buildO` docs).
  weakLeancArgs := #["-I", orToolsInclude.toString]
  -- `SolveCpModelWithParameters` et al. (`cp_solver_c.h`) are exported from
  -- the `ortools_core` library, not `ortools` itself, so both must be linked.
  weakLinkArgs := #[
    "-L", orToolsLib.toString, "-lortools", "-lortools_core", s!"-Wl,-rpath,{orToolsLib}"
  ]

-- Pinned to a commit, not a tag: upstream has no tagged releases as of this
-- writing. Validated against this project's lean-toolchain (v4.32.2) despite
-- protobuf's own lean-toolchain being v4.32.0.
require protobuf from git
  "https://github.com/Lean-zh/protobuf.git" @ "b6af3753a1e9f12269039e1322bf3020175d7577"

@[default_target]
lean_lib Cpsat

/--
The C++ shim over CP-SAT's own `cp_solver_c.h` C API: bytes in, bytes out.

Built with the system C++ compiler via `buildO`, not `buildLeanO`: the latter
compiles with Lean's bundled clang under `-nostdinc --sysroot <lean-toolchain>`,
which has no C++ standard library headers, since it's meant for Lean's own
generated C output rather than hand-written C++.
-/
extern_lib cpsatShim pkg := do
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cpsat_shim.cpp"
  let oFile := pkg.buildDir / "native" / "cpsat_shim.o"
  let weakArgs :=
    #["-I", orToolsInclude.toString, "-I", (← getLeanIncludeDir).toString, "-std=c++20", "-fPIC"]
  let oJob ← buildO oFile srcJob weakArgs (compiler := "c++")
  buildStaticLib (pkg.buildDir / "native" / "libcpsat_shim.a") #[oJob]

/--
Compile-only check, never linked into anything: cross-checks the field
numbers hand-declared in `Cpsat/Proto.lean` against protoc's own generated
constants in `cp_model.pb.h`/`sat_parameters.pb.h`. `@[default_target]` so it
runs on every plain `lake build`, not just when something happens to link the
shim (`cpsatShim` itself only gets built on demand, e.g. by `lake test`).

Needs a much wider include path than `cpsatShim`: unlike `cp_solver_c.h` (pure
C, no protobuf), `cp_model.pb.h` is protoc-generated C++ pulling in the
in-tree protobuf/abseil headers OR-Tools built against - the exact flags CMake
itself uses to compile `cp_model.pb.cc`, per `or-tools/build/compile_commands.json`.
-/
@[default_target]
extern_lib cpsatFieldNumberCheck pkg := do
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cpsat_field_numbers_check.cpp"
  let oFile := pkg.buildDir / "native" / "cpsat_field_numbers_check.o"
  let deps := orToolsBuild / "_deps"
  let weakArgs := #[
    "-I", orToolsInclude.toString,
    "-I", orToolsBuild.toString,
    "-isystem", (deps / "protobuf-src" / "src").toString,
    "-isystem", (deps / "absl-src").toString,
    "-isystem", (deps / "protobuf-src" / "third_party" / "utf8_range").toString,
    "-DOR_ORTOOLS_PROTO_DLL=", "-std=c++20", "-fPIC"
  ]
  let oJob ← buildO oFile srcJob weakArgs (compiler := "c++")
  buildStaticLib (pkg.buildDir / "native" / "libcpsat_field_numbers_check.a") #[oJob]

@[test_driver]
lean_exe test where
  root := `Test.Main
  supportInterpreter := true
