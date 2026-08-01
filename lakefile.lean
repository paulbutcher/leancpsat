-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Lake
open Lake DSL System

/--
Find the single OR-Tools C++ SDK directory the user is expected to have
downloaded and extracted under `or-tools/` (its name is version- and
platform-specific, so it can't be hardcoded here).
-/
def findOrToolsSdk (base : FilePath) : IO FilePath := do
  unless (← base.pathExists) do
    throw <| IO.userError s!"{base} does not exist. Download the OR-Tools C++ SDK release for this platform and extract it there before building."
  let mut candidates : Array FilePath := #[]
  for entry in (← base.readDir) do
    let p := entry.path
    if (← p.isDir) then
      if (← (p / "include" / "ortools" / "sat" / "cp_model.h").pathExists) then
        candidates := candidates.push p
  if candidates.size == 1 then
    return candidates[0]!
  else if candidates.isEmpty then
    throw <| IO.userError s!"No OR-Tools SDK found under {base}. Download the release for this platform and extract it there before building."
  else
    throw <| IO.userError s!"Multiple OR-Tools SDKs found under {base} ({candidates}); expected exactly one."

def orToolsSdk : FilePath := run_io findOrToolsSdk (__dir__ / "or-tools")
def orToolsInclude : FilePath := orToolsSdk / "include"
def orToolsLib : FilePath := orToolsSdk / "lib"

package cpsat where
  version := v!"0.1.0"
  -- Weak: these embed a local, machine-specific path, so they must not affect
  -- build artifact hashes (see Lake's `buildO` docs).
  weakLeancArgs := #["-I", orToolsInclude.toString]
  weakLinkArgs := #[
    "-L", orToolsLib.toString, "-lortools", s!"-Wl,-rpath,{orToolsLib}"
  ]

-- Pinned to a commit, not a tag: upstream has no tagged releases as of this
-- writing. Validated against this project's lean-toolchain (v4.32.2) despite
-- protobuf's own lean-toolchain being v4.32.0.
require protobuf from git
  "https://github.com/Lean-zh/protobuf.git" @ "b6af3753a1e9f12269039e1322bf3020175d7577"

@[default_target]
lean_lib Cpsat

/-- The C++ shim over CP-SAT's own `cp_solver_c.h` C API: bytes in, bytes out. -/
extern_lib cpsatShim pkg := do
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cpsat_shim.cpp"
  let oFile := pkg.buildDir / "native" / "cpsat_shim.o"
  let weakArgs := #["-I", orToolsInclude.toString, "-std=c++20"]
  let oJob ← buildLeanO oFile srcJob weakArgs
  buildStaticLib (pkg.buildDir / "native" / "libcpsat_shim.a") #[oJob]

@[test_driver]
lean_exe test where
  root := `Test.Main
  supportInterpreter := true
