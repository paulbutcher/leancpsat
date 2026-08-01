<!-- Copyright (c) 2026 Paul Butcher. All rights reserved.
     Released under Apache 2.0 license as described in the file LICENSE. -->

# Project plan: Tier-1 constraint kinds

Scope: implement the remaining CP-SAT constraint kinds that fit the existing design
(`DESIGN.md`) without any new structural concepts - no new handle type, no incremental
sub-builder, just a message declaration in `Cpsat.Proto` plus a single `addX` function in
`Cpsat.Model`, mirroring the matching `CpModelBuilder::AddXXX` method in `cp_model.h`.

## Baseline (already in the v1 design, not part of this plan)

`linear` (`LinearConstraintProto`), `all_diff` (`AllDifferentConstraintProto`), `bool_or`,
`bool_and`, `at_most_one`, `exactly_one` (all four backed by the same
`BoolArgumentProto`).

## In scope for this plan

Confirmed against `cp_model.pb.h`/`cp_model.h`: each of these is a single `CpModelBuilder::AddXXX`
call returning a plain `Constraint` (no specialized subtype, no `IntervalVar` involved).

| Oneof case | Backing message         | C++ builder method(s)                                   |
|------------|--------------------------|----------------------------------------------------------|
| `bool_xor` | `BoolArgumentProto`      | `AddBoolXor`                                              |
| `element`  | `ElementConstraintProto` | `AddElement` (×3 overloads), `AddVariableElement`         |
| `inverse`  | `InverseConstraintProto` | `AddInverseConstraint`                                    |
| `lin_max`  | `LinearArgumentProto`    | `AddMaxEquality` (×3), `AddMinEquality` (×3, negate client-side), `AddAbsEquality` (unconfirmed - see task 6) |
| `int_div`  | `LinearArgumentProto`    | `AddDivisionEquality`                                      |
| `int_mod`  | `LinearArgumentProto`    | `AddModuloEquality`                                        |
| `int_prod` | `LinearArgumentProto`    | `AddMultiplicationEquality` (×4 overloads)                 |

`bool_xor` reuses `BoolArgumentProto`, already declared for the baseline kinds - it is the
smallest possible addition (one field number, one builder function). `lin_max`/`int_div`/
`int_mod`/`int_prod` all share `LinearArgumentProto`'s shape (a target expression plus a
list of operand expressions), so declaring that message once covers four oneof cases.

## Tasks

Each task is independent of the others (they only ever add to `Cpsat.Model`/`Cpsat.Proto`
using types - `IntVar`, `BoolVar`, `LinearExpr`, `Constraint` - that already exist), so
they can be done in any order or picked up in parallel. Suggested order below is by
expected real-world usage frequency, most useful first.

**Task 0 - prerequisite, blocks everything below. Done.**
`Cpsat.Proto`/`Cpsat.Solver` land the baseline constraint kinds end to end through
`solve`, exercised by `Test/Main.lean` (`lake test`); see `DESIGN.md` §7 for how its open
questions were resolved. The remaining tasks in this plan are unstarted. Originally:
confirm `Lean-zh/protobuf` (`lean-toolchain v4.32.0`) builds as a dependency of this
package (`lean-toolchain v4.32.2`), and get the v1 constraint kinds (baseline above) landed end to
end through `solve`. Nothing in this plan can start before that path exists, since every
task below only adds to `Cpsat.Proto`/`Cpsat.Model`, which don't exist yet until v1 is in.

**Task 1 - `lin_max` (max, and min via negation). Done.**
- Declare `LinearArgumentProto` (`target`, `exprs`) in `Cpsat.Proto`, field numbers from
  `cp_model.pb.h`.
- `addMaxEquality (target : LinearExpr) (exprs : Array LinearExpr) : CpModelM Constraint`
- `addMinEquality (target : LinearExpr) (exprs : Array LinearExpr) : CpModelM Constraint`
  implemented by negating `target` and each of `exprs` and calling `addMaxEquality`
  (matches how the C++ builder itself derives min from max - confirm against
  `cp_model.h`'s implementation, not just the declared signatures, before assuming this).
- Test: three variables, known min/max, assert solver picks it correctly.

**Task 2 - `element`. Done.**
- Declare `ElementConstraintProto` in `Cpsat.Proto`.
- `addElement (index : LinearExpr) (exprs : Array LinearExpr) (target : LinearExpr) : CpModelM Constraint`
  (covers the "array of expressions" overload; the "array of int64 values" and
  "array of IntVar" overloads in C++ are convenience wrappers - can be added as thin Lean
  wrappers over the same message once the core case works, not separate tasks).
- Test: `target = exprs[index]` for a small fixed array.

**Task 3 - `int_div`.**
- Reuses `LinearArgumentProto` (already declared in Task 1).
- `addDivisionEquality (target numerator denominator : LinearExpr) : CpModelM Constraint`
- Test: integer division with a known quotient, including a case with a negative
  numerator (verifies CP-SAT's rounding convention is what we expect - confirm against
  documentation/solver behavior, not assumption).

**Task 4 - `int_mod`.**
- Reuses `LinearArgumentProto`.
- `addModuloEquality (target expr modulus : LinearExpr) : CpModelM Constraint`
- Test: modulo with a known remainder.

**Task 5 - `int_prod`.**
- Reuses `LinearArgumentProto`.
- `addMultiplicationEquality (target : LinearExpr) (factors : Array LinearExpr) : CpModelM Constraint`
  (covers the general "array of factors" case; the two-factor overload is a thin wrapper).
- Test: `target = a * b` for two small int vars.

**Task 6 - `inverse`.**
- Declare `InverseConstraintProto` in `Cpsat.Proto`.
- `addInverseConstraint (vars invVars : Array IntVar) : CpModelM Constraint`
- Test: a small permutation and its known inverse.

**Task 7 - `bool_xor`.**
- No new message declaration (reuses `BoolArgumentProto`); purely a new field number plus
  a new builder function.
- `addBoolXor (lits : Array BoolVar) : CpModelM Constraint`
- Test: odd/even parity over a few bool vars.

**Task 8 - `abs_equality` (verify placement first).**
`AddAbsEquality` is a single-call, `Constraint`-returning method like the rest of this
plan, but which oneof case backs it isn't confirmed from the header alone (it may lower
to `lin_max` client-side, e.g. `abs(x) = max(x, -x)`, or something else). First step is
reading the OR-Tools *implementation* (not just the header) to confirm, then:
- `addAbsEquality (target expr : LinearExpr) : CpModelM Constraint`
- Test: known absolute-value cases including a negative input.

Each task's definition of done: message declared in `Cpsat.Proto` with field numbers
cited against the vendored header, builder function(s) added to `Cpsat.Model` with naming
matching the C++ method being mirrored, and at least one passing `lake test` case with a
known expected result (not just "solver returns `OPTIMAL`" - assert the actual values).

## Remaining - not covered by this plan

These need design work beyond "declare a message and add a function," per the earlier
tier breakdown, and are explicitly out of scope here:

- **Needs `IntervalVar` as a new first-class handle type first** (not yet designed):
  `interval`, `no_overlap`, `no_overlap_2d`, `cumulative`. `no_overlap` is otherwise a
  single-call constraint (`AddNoOverlap(Span<IntervalVar>)`), so once `IntervalVar` exists
  it likely becomes a Tier-1-shaped task; `no_overlap_2d` and `cumulative` also need
  Task-group-2 below regardless.
- **Needs a Lean equivalent of the incremental sub-builder pattern** (specialized handle
  type with its own follow-up methods, e.g. `TableConstraint.addTuple`): `circuit`
  (`CircuitConstraint.AddArc`), `table` (`TableConstraint.AddTuple`), `automaton`
  (`AutomatonConstraint.AddTransition`), `reservoir`
  (`ReservoirConstraint.AddEvent`/`AddOptionalEvent`), plus `no_overlap_2d`
  (`NoOverlap2DConstraint.AddRectangle`) and `cumulative`
  (`CumulativeConstraint.AddDemand`), both of which are also blocked on `IntervalVar`.
- **`routes` has no `CpModelBuilder` method to mirror at all** - grepped `cp_model.h` and
  confirmed there is no `AddRoutes`/similar public builder method, unlike every other
  oneof case. Supporting it means designing a Lean API from the `RoutesConstraintProto`
  shape directly with no C++ builder precedent to copy, which is more design work than
  any kind in this plan or the two groups above.
- **`dummy_constraint`** - internal presolve bookkeeping, not something a model author
  constructs. Permanently out of scope; no user-facing purpose.
