# cpsat

Lean bindings for the [OR-Tools](https://developers.google.com/optimization)' CP-SAT
constraint solver.

## Usage

```lean
import Cpsat

open Cpsat

def main : IO Unit := do
  let ((rabbits, pheasants), resp) ← solve (m := do
    let rabbits   ← newIntVar (.ofInterval 0 20) "rabbits"
    let pheasants ← newIntVar (.ofInterval 0 20) "pheasants"
    let _ ← addEquality (rabbits + pheasants) (.const 20)
    let _ ← addEquality ((4 : Int64) * rabbits + (2 : Int64) * pheasants) (.const 56)
    pure (rabbits, pheasants))
  match resp.status with
  | .optimal | .feasible =>
    IO.println s!"rabbits = {resp.value rabbits}, pheasants = {resp.value pheasants}"
  | _ => IO.println "no solution"
```

`solve` takes an optional `SolverParameters` (time limit, worker count, random seed,
whether to log search progress) and returns whatever your model-building computation
returned, paired with the `CpSolverResponse` (status, objective value, solution
values, timing). `solveInterruptible` is the same, but cooperatively cancellable via a
`StopToken` from another task.

See `Test/Main.lean` for a worked example of every constraint kind below, each with a
known expected result asserted against the actual solver.

## What's covered

Variables and expressions:

- `newIntVar`/`newBoolVar`/`newConstant`, closed-interval `Domain`s
- `LinearExpr`: affine combinations of variables via `+`, `-`, `*`, negation, and
  coercions from `IntVar`/`BoolVar`

Constraints:

- Linear: `addLinearConstraint`, `addEquality`, `addLessOrEqual`, `addGreaterOrEqual`,
  `addNotEqual`
- Boolean logic: `addBoolOr`, `addBoolAnd`, `addAtMostOne`, `addExactlyOne`,
  `addBoolXor`, `addImplication`
- `addAllDifferent`
- `addMaxEquality`/`addMinEquality` (`lin_max`; min is derived by negation, the same
  way CP-SAT's own C++ builder derives it)
- `addAbsEquality` (also derived from `lin_max`, again mirroring the C++ builder)
- `addElement` (`exprs[index] == target`)
- `addDivisionEquality`, `addModuloEquality` (both rounded/signed towards zero, per
  CP-SAT's documented convention), `addMultiplicationEquality`
- `addInverseConstraint`
- `Constraint.onlyEnforceIf` (half-reification via enforcement literals)

Objectives: `minimize`/`maximize` over a `LinearExpr`.

## What's not yet covered

- `interval`, `no_overlap`, `no_overlap_2d`, `cumulative`
- `circuit`, `table`, `automaton`, `reservoir`
- `routes`, `dummy_constraint`
- Most of `SatParameters` (`SolverParameters` currently exposes only time limit,
  worker count, random seed, and search-progress logging)

## Building

This project includes and builds OR-Tools from source. The first build can take well
over an hour; Subsequent builds will be faster. The [OR-Tools prerequisites](https://developers.google.com/optimization/install/cpp) are required.

### Troubleshooting

If the OR-Tools build fails (likely due to limited memory) try restricting
the number of cmake jobs with:

```sh
env LEANCPSAT_ORTOOLS_JOBS=2 lake build
```

## Using cpsat as a dependency

```lean
require cpsat from git
  "https://github.com/paulbutcher/leancpsat" @ "main"
```

plus a normal `lean_exe` that `import`s `Cpsat` is all a consumer needs; no extra
linker configuration is required in the consumer's own `lakefile.lean`. See
`Test/downstream-consumer/` for a minimal, tested example.

This works despite Lake never propagating a package's `weakLinkArgs`/`weakLeancArgs`
to a consumer that merely `require`s it (those two fields only apply to targets built
inside the declaring package itself, so they *wouldn't* help a consumer). Instead,
this package's `lakefile.lean` attaches the `-I`/`-L`/`-l`/`-rpath` flags needed for
the vendored, locally-built OR-Tools to two other fields, `moreLinkLibs` and
`moreLinkObjs`, which Lake *does* collect transitively: `LeanExe.recBuildExe` (in
Lake's `Build/Executable.lean`) gathers `moreLinkLibs`/`moreLinkObjs` from the owning
library of every module a `lean_exe` transitively imports, not just from the
executable's own package. That's the same mechanism that already makes this package's
`cpsatShim` C++ shim (an `extern_lib`) link into a consumer for free: Lake also always
collects every transitive dependency's `extern_lib` static archives into an
executable's link line, unconditionally. Only the additional OR-Tools flags needed
propagating explicitly, which is what `moreLinkLibs`/`moreLinkObjs` are for.

## License

Apache License 2.0 - see [LICENSE](LICENSE). OR-Tools itself (vendored under
`or-tools/`) is also Apache 2.0 licensed; see `or-tools/LICENSE`.
