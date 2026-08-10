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

def orToolsDir : FilePath := __dir__ / "or-tools"
def orToolsBuild : FilePath := run_io findOrToolsBuild orToolsDir
def orToolsInclude : FilePath := orToolsDir
def orToolsLib : FilePath := orToolsBuild / "lib"
def orToolsDeps : FilePath := orToolsBuild / "_deps"

/-- The bare library names (`Cbc` from `libCbc.so.2`) `ldd` reports as
`NEEDED` by the given shared library. -/
def lddNeededNames (lib : FilePath) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "ldd", args := #[lib.toString] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"`ldd {lib}` failed:\n{out.stderr}"
  let mut names := #[]
  for line in out.stdout.splitOn "\n" do
    let fields := line.splitOn "=>"
    if fields.length > 1 then
      let soname := fields[0]!.trimAscii.toString
      if soname.startsWith "lib" then
        names := names.push ((soname.drop 3).toString.splitOn ".so")[0]!
  return names

-- Elaboration-time only: the actual `Dynlib` values (`orToolsCoreDeps` below) are built from
-- this via a plain, non-`IO` `def`, since `Dynlib` (unlike `Array String`) has no `ToExpr`
-- instance for `run_io` to embed a computed value of that type as a literal term.
def orToolsCoreDepNames : Array String :=
  run_io lddNeededNames (orToolsLib / nameToSharedLib "ortools_core")

/-- Every shared library `libortools_core.so` itself depends on (absl,
protobuf, the solver backends it links against, ...), as `Dynlib` values
pointing into `orToolsLib` (where OR-Tools' CMake build places every shared
library it produces or vendors, including these) - except `stdc++`, handled
separately by `systemLibStdCxx` below (see its docstring for why). Needed
because `cpsatShim` now links directly against OR-Tools' advanced C++ API
(`Model`, `SolveCpModel`, `NewFeasibleSolutionObserver`) for the streaming
solve, not just the trimmed C API (`cp_solver_c.h`): any translation unit
that instantiates absl/protobuf's header-only template code needs the
specific `.so` providing the matching out-of-line symbols linked in
directly, since the static linker (unlike the runtime loader) doesn't chase
another library's own dependencies to resolve undefined symbols. Read from
`ldd` rather than hand-listed so an OR-Tools version bump that adds or
renames a dependency doesn't silently break the link. -/
def orToolsCoreDeps : Array Dynlib :=
  (orToolsCoreDepNames.filter (· != "stdc++")).map
    fun name => {path := orToolsLib / nameToSharedLib name, name}

/-- The absolute path to the system's real GNU libstdc++, its fully-versioned filename rather
than the bare `libstdc++.so`, which commonly resolves to a linker script rather than a real
shared object.

`cpsatShim` is compiled with the system C++ compiler (see its docstring for why) and so needs
real libstdc++ symbols (`std::thread`, `std::condition_variable`, ...), but Lean's own bundled
`clang` has no libstdc++ at all: it targets `libc++`, and - subtly - silently substitutes its own
bundled `libc++`/`libc++abi`/`libunwind` for a plain `-lstdc++` link flag rather than erroring or
finding the system one, so that flag alone doesn't work here. An absolute path bypasses this
substitution entirely. -/
def systemLibStdCxx : FilePath :=
  run_io do
    let out ← IO.Process.output { cmd := "c++", args := #["-print-file-name=libstdc++.so.6"] }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"failed to locate the system's libstdc++.so.6:\n{out.stderr}"
    return FilePath.mk out.stdout.trimAscii.toString

/-- The directory containing the system's `libgcc.a`, GCC's own low-level runtime support
library (division helpers, unwind glue, ...).

On some platforms (observed on x86_64 CI; not the aarch64 machine this was developed on), the
bare `libgcc_s.so` found via the default search path isn't a real shared object but a GNU ld
linker script (`GROUP ( libgcc_s.so.1 -lgcc )`); resolving the `-lgcc_s` this project (and Lean's
own default link flags) already need can therefore transitively require finding `-lgcc` too,
which isn't anywhere on the search path Lean's own bundled `clang`/`--sysroot` looks under
(`ld.lld: error: unable to find library -lgcc`, with no `-lgcc` on the command line at all -
it's pulled in by that script). Adding this directory to the search path lets it resolve. -/
def systemLibGccDir : FilePath :=
  run_io do
    let out ← IO.Process.output { cmd := "c++", args := #["-print-file-name=libgcc.a"] }
    unless out.exitCode == 0 do
      throw <| IO.userError s!"failed to locate the system's libgcc.a:\n{out.stderr}"
    let path := FilePath.mk out.stdout.trimAscii.toString
    match path.parent with
    | some dir => return dir
    | none => throw <| IO.userError s!"libgcc.a path {path} has no parent directory"

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
  -- The flags above only apply to *this* package's own targets (Lake does not
  -- propagate `weakLeancArgs`/`weakLinkArgs` across a `require`). `moreLinkLibs`
  -- and `moreLinkObjs`, by contrast, are collected from the owning library of
  -- every module a consumer transitively imports (`LeanExe.recBuildExe` in
  -- `Lake/Build/Executable.lean`), the same mechanism that already makes
  -- `cpsatShim`'s static archive show up on a consumer's link line for free.
  -- Duplicating the OR-Tools link inputs here, as target references rather
  -- than raw path strings, is what actually makes a `require`-only consumer
  -- link: see `orToolsOrtoolsDynlib` et al. below.
  moreLinkLibs := #[
    (BuildKey.packageTarget .anonymous `orToolsOrtoolsDynlib : Target Dynlib),
    (BuildKey.packageTarget .anonymous `orToolsOrtoolsCoreDynlib : Target Dynlib)
  ]
  moreLinkObjs := #[
    (BuildKey.packageTarget .anonymous `orToolsRpathFlag : Target FilePath),
    (BuildKey.packageTarget .anonymous `systemLibStdCxxFlag : Target FilePath),
    (BuildKey.packageTarget .anonymous `systemLibGccDirFlag : Target FilePath),
    (BuildKey.packageTarget .anonymous `allowShlibUndefinedFlag : Target FilePath)
  ]

-- Pinned to a commit, not a tag: upstream has no tagged releases as of this
-- writing. Validated against this project's lean-toolchain (v4.32.2) despite
-- protobuf's own lean-toolchain being v4.32.0.
require protobuf from git
  "https://github.com/Lean-zh/protobuf.git" @ "b6af3753a1e9f12269039e1322bf3020175d7577"

@[default_target]
lean_lib Cpsat

/--
The C++ shim over CP-SAT's C APIs: bytes in, bytes out.

Built with the system C++ compiler via `buildO`, not `buildLeanO`: the latter
compiles with Lean's bundled clang under `-nostdinc --sysroot <lean-toolchain>`,
which has no C++ standard library headers, since it's meant for Lean's own
generated C output rather than hand-written C++.

Needs the same wider include path as `cpsatFieldNumberCheck` (protobuf/absl
headers, not just `cp_solver_c.h`'s pure-C API), since the streaming solve
calls OR-Tools' advanced C++ API (`cp_model_solver.h`) directly. `-DNDEBUG`
must match how OR-Tools' own build compiled these headers
(`or-tools/build/compile_commands.json`): several absl/protobuf class layouts
are conditional on it, and a mismatch corrupts memory silently rather than
failing to compile or link.
-/
extern_lib cpsatShim pkg := do
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cpsat_shim.cpp"
  let oFile := pkg.buildDir / "native" / "cpsat_shim.o"
  let weakArgs := #[
    "-I", orToolsInclude.toString,
    "-I", orToolsBuild.toString,
    "-I", (← getLeanIncludeDir).toString,
    "-isystem", (orToolsDeps / "protobuf-src" / "src").toString,
    "-isystem", (orToolsDeps / "absl-src").toString,
    "-isystem", (orToolsDeps / "protobuf-src" / "third_party" / "utf8_range").toString,
    "-DOR_ORTOOLS_PROTO_DLL=", "-DNDEBUG", "-std=c++20", "-fPIC", "-pthread"
  ]
  let oJob ← buildO oFile srcJob weakArgs (compiler := "c++")
  buildStaticLib (pkg.buildDir / "native" / "libcpsat_shim.a") #[oJob]

/-- Referenced by `package cpsat`'s `moreLinkLibs` (propagates `-L`/`-l` for
`libortools.so` to any transitive importer of `Cpsat`, including consumers
that merely `require` this package). -/
target orToolsOrtoolsDynlib _pkg : Dynlib := do
  return .pure {path := orToolsLib / nameToSharedLib "ortools", name := "ortools"}

/-- As `orToolsOrtoolsDynlib`, for `libortools_core.so` (see the comment on
`weakLinkArgs` above for why both are needed). Carries `orToolsCoreDeps` as
`deps` so `Lake.mkLinkOrder` (which every `buildLeanExe` call consults, not
just this package's own) flattens them onto any consuming executable's link
line too, without needing a separate named target per library. -/
target orToolsOrtoolsCoreDynlib _pkg : Dynlib := do
  return .pure {
    path := orToolsLib / nameToSharedLib "ortools_core", name := "ortools_core"
    deps := orToolsCoreDeps
  }

/-- Referenced by `package cpsat`'s `moreLinkObjs`. `moreLinkObjs` entries are
spliced verbatim onto the linker command line (`mkLinkObjArgs` in
`Lake/Build/Common.lean` just calls `toString` on each and pushes it), so a
raw `-Wl,-rpath,...` flag round-trips through it unchanged; there's no
dedicated propagating field for arbitrary linker flags, and `Dynlib` (the type
`moreLinkLibs` deals in) has no rpath slot. Without this, a consumer's binary
links but can't find `libortools.so` at runtime. -/
target orToolsRpathFlag _pkg : FilePath := do
  return .pure (FilePath.mk s!"-Wl,-rpath,{orToolsLib}")

/-- As `orToolsRpathFlag`, splicing `systemLibStdCxx`'s absolute path onto the link line via
`moreLinkObjs` (see its docstring for why a bare `-lstdc++` doesn't work here) - wrapped in
`-Wl,` rather than passed as a bare positional argument, so `clang`'s driver forwards it to the
linker completely opaquely instead of inspecting it as an input file. -/
target systemLibStdCxxFlag _pkg : FilePath := do
  return .pure (FilePath.mk s!"-Wl,{systemLibStdCxx}")

/-- As `orToolsRpathFlag`, adding `systemLibGccDir` to the link search path (see its docstring
for why). -/
target systemLibGccDirFlag _pkg : FilePath := do
  return .pure (FilePath.mk s!"-L{systemLibGccDir}")

/-- As `orToolsRpathFlag`, splicing `-Wl,--allow-shlib-undefined` onto the link line: several of
`orToolsCoreDeps` (e.g. `libabsl_exponential_biased.so`, which calls `log2`) were built against a
newer glibc than the one Lean's own bundled `clang` links against by default, so the static
linker sees them as having their own unresolved symbols. That's fine - those symbols are meant to
be resolved by the *dynamic* loader against the system's actual glibc at run time, exactly as
they already are for the OR-Tools shared libraries this project depended on before the streaming
solve existed; this flag just tells the static linker not to treat that as an error. It does not
weaken checking of `cpsatShim`'s own symbols, only of other shared libraries' internal ones. -/
target allowShlibUndefinedFlag _pkg : FilePath := do
  return .pure (FilePath.mk "-Wl,--allow-shlib-undefined")

/--
Compile-only check, never linked into anything: cross-checks the field
numbers hand-declared in `Cpsat/Proto.lean` against protoc's own generated
constants in `cp_model.pb.h`/`sat_parameters.pb.h`. `@[default_target]` so it
runs on every plain `lake build`, not just when something happens to link the
shim (`cpsatShim` itself only gets built on demand, e.g. by `lake test`).

`cp_model.pb.h` is protoc-generated C++ pulling in the in-tree protobuf/abseil
headers OR-Tools built against - the exact flags CMake itself uses to compile
`cp_model.pb.cc`, per `or-tools/build/compile_commands.json` (the same ones
`cpsatShim` now needs too, for the same reason).
-/
@[default_target]
extern_lib cpsatFieldNumberCheck pkg := do
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cpsat_field_numbers_check.cpp"
  let oFile := pkg.buildDir / "native" / "cpsat_field_numbers_check.o"
  let weakArgs := #[
    "-I", orToolsInclude.toString,
    "-I", orToolsBuild.toString,
    "-isystem", (orToolsDeps / "protobuf-src" / "src").toString,
    "-isystem", (orToolsDeps / "absl-src").toString,
    "-isystem", (orToolsDeps / "protobuf-src" / "third_party" / "utf8_range").toString,
    "-DOR_ORTOOLS_PROTO_DLL=", "-std=c++20", "-fPIC"
  ]
  let oJob ← buildO oFile srcJob weakArgs (compiler := "c++")
  buildStaticLib (pkg.buildDir / "native" / "libcpsat_field_numbers_check.a") #[oJob]

@[test_driver]
lean_exe test where
  root := `Test.Main
  supportInterpreter := true
