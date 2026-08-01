-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Cpsat

/-!
End-to-end tests through `Cpsat.solve`: these are the real proof that the FFI
boundary and linking (`native/cpsat_shim.cpp` against the vendored OR-Tools
build) are correct, not just that the pure Lean layers type check.
-/

open Cpsat

def assert (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

def assertEq [BEq α] (actual expected : α) (label : String) : IO Unit :=
  assert (actual == expected) label

/-- The canonical "rabbits and pheasants" CP-SAT sample: a unique-solution
feasibility problem with no objective. -/
def testRabbitsAndPheasants : IO Unit := do
  let ((rabbits, pheasants), resp) ← solve (m := do
    let rabbits ← newIntVar (.ofInterval 0 20) "rabbits"
    let pheasants ← newIntVar (.ofInterval 0 20) "pheasants"
    let _ ← addEquality (rabbits + pheasants) (.const 20)
    let _ ← addEquality ((4 : Int64) * rabbits + (2 : Int64) * pheasants) (.const 56)
    pure (rabbits, pheasants))
  assertEq resp.status .optimal "rabbitsAndPheasants: expected optimal"
  assertEq (resp.value rabbits) (8 : Int64) "rabbitsAndPheasants: expected 8 rabbits"
  assertEq (resp.value pheasants) (12 : Int64) "rabbitsAndPheasants: expected 12 pheasants"

/-- A linear objective: minimize `x + y` subject to `x + y >= 5`, `x <= 3`. -/
def testObjective : IO Unit := do
  let ((x, y), resp) ← solve (m := do
    let x ← newIntVar (.ofInterval 0 10) "x"
    let y ← newIntVar (.ofInterval 0 10) "y"
    let _ ← addGreaterOrEqual (x + y) (.const 5)
    let _ ← addLessOrEqual x (.const 3)
    minimize (x + y)
    pure (x, y))
  assertEq resp.status .optimal "objective: expected optimal"
  assertEq resp.objectiveValue (5.0 : Float) "objective: expected value 5"
  assertEq ((resp.value x) + (resp.value y)) (5 : Int64) "objective: expected x + y = 5"

/-- Maximize instead of minimize, to exercise the sign flip in
`Cpsat.Proto.objectiveToProto`. -/
def testMaximize : IO Unit := do
  let (x, resp) ← solve (m := do
    let x ← newIntVar (.ofInterval 0 10) "x"
    let _ ← addLessOrEqual x (.const 7)
    maximize (x + LinearExpr.const 1)
    pure x)
  assertEq resp.status .optimal "maximize: expected optimal"
  assertEq (resp.value x) (7 : Int64) "maximize: expected x = 7"
  assertEq resp.objectiveValue (8.0 : Float) "maximize: expected objective value 8"

def testAllDifferent : IO Unit := do
  let (vars, resp) ← solve (m := do
    let vars ← #[(), (), ()].mapM fun _ => newIntVar (.ofInterval 0 2)
    let _ ← addAllDifferent vars
    pure vars)
  assertEq resp.status .optimal "allDifferent: expected optimal"
  let values := (vars.map resp.value).qsort (· < ·)
  assertEq values #[0, 1, 2] "allDifferent: expected {0,1,2} in some order"

/-- `exactlyOne` over three literals forces exactly one true. -/
def testExactlyOne : IO Unit := do
  let (lits, resp) ← solve (m := do
    let lits ← #[(), (), ()].mapM fun _ => newBoolVar
    let _ ← addExactlyOne lits
    pure lits)
  assertEq resp.status .optimal "exactlyOne: expected optimal"
  let trueCount := (lits.filter fun b => resp.solution.getD b.literal.toNat 0 == 1).size
  assertEq trueCount 1 "exactlyOne: expected exactly one true literal"

/-- `addMaxEquality`/`addMinEquality` over three fixed values: known max and
min. `addMinEquality` is implemented via negation of `addMaxEquality`
(`Cpsat.Model.addMinEquality`), so this exercises that derivation too, not
just `lin_max` itself. -/
def testLinMax : IO Unit := do
  let ((maxVar, minVar), resp) ← solve (m := do
    let a ← newConstant 3
    let b ← newConstant 7
    let c ← newConstant 5
    let maxVar ← newIntVar (.ofInterval 0 10)
    let minVar ← newIntVar (.ofInterval 0 10)
    let vals := #[LinearExpr.ofIntVar a, LinearExpr.ofIntVar b, LinearExpr.ofIntVar c]
    let _ ← addMaxEquality (.ofIntVar maxVar) vals
    let _ ← addMinEquality (.ofIntVar minVar) vals
    pure (maxVar, minVar))
  assertEq resp.status .optimal "linMax: expected optimal"
  assertEq (resp.value maxVar) (7 : Int64) "linMax: expected max = 7"
  assertEq (resp.value minVar) (3 : Int64) "linMax: expected min = 3"

/-- Infeasible model: `x <= 1` and `x >= 5` over a domain that admits both. -/
def testInfeasible : IO Unit := do
  let (_, resp) ← solve (m := do
    let x ← newIntVar (.ofInterval 0 10) "x"
    let _ ← addLessOrEqual x (.const 1)
    let _ ← addGreaterOrEqual x (.const 5)
    pure x)
  assertEq resp.status .infeasible "infeasible: expected infeasible"

def main : IO Unit := do
  testRabbitsAndPheasants
  testObjective
  testMaximize
  testAllDifferent
  testExactlyOne
  testLinMax
  testInfeasible
  IO.println "All tests passed."
