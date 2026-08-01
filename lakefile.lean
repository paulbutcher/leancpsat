-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Lake
open Lake DSL System

/--
Locate the OR-Tools checkout under `or-tools/` and its CMake build tree.
`or-tools/` is a full source checkout (not a downloaded prebuilt SDK: see
`notes.txt` for the `cmake -S . -B build ...` invocation used to build it), so
headers live at `or-tools/ortools/...` and the built shared libraries live at
`or-tools/build/lib`.
-/
def findOrToolsBuild (orToolsDir : FilePath) : IO FilePath := do
  let header := orToolsDir / "ortools" / "sat" / "cp_model.h"
  unless (← header.pathExists) do
    throw <| IO.userError s!"{header} not found. Expected a full OR-Tools source checkout under {orToolsDir}."
  let buildDir := orToolsDir / "build"
  let lib := buildDir / "lib" / "libortools.so"
  unless (← lib.pathExists) do
    throw <| IO.userError s!"{lib} not found. Build OR-Tools first: cmake -S {orToolsDir} -B {buildDir} -DBUILD_DEPS=ON ... && cmake --build {buildDir}."
  return buildDir

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
  -- `libortools_core.so`, not `libortools.so` itself, so both must be linked.
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

@[test_driver]
lean_exe test where
  root := `Test.Main
  supportInterpreter := true
