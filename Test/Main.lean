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

/-- `target = exprs[index]` for a small fixed array of constant values. -/
def testElement : IO Unit := do
  let (target, resp) ← solve (m := do
    let index ← newConstant 2
    let target ← newIntVar (.ofInterval 0 100)
    let exprs := #[10, 20, 30, 40].map (LinearExpr.const ·)
    let _ ← addElement (.ofIntVar index) exprs (.ofIntVar target)
    pure target)
  assertEq resp.status .optimal "element: expected optimal"
  assertEq (resp.value target) (30 : Int64) "element: expected exprs[2] = 30"

/-- `target == numerator / denominator`, rounded towards zero. The negative
numerator case pins down that rounding convention: `-10 / 3 = -3`, not the
floor-division `-4`. -/
def testDivision : IO Unit := do
  let (target1, resp1) ← solve (m := do
    let numerator ← newConstant 12
    let denominator ← newConstant 5
    let target ← newIntVar (.ofInterval (-20) 20)
    let _ ← addDivisionEquality (.ofIntVar target) (.ofIntVar numerator) (.ofIntVar denominator)
    pure target)
  assertEq resp1.status .optimal "division: expected optimal (12 / 5)"
  assertEq (resp1.value target1) (2 : Int64) "division: expected 12 / 5 = 2"

  let (target2, resp2) ← solve (m := do
    let numerator ← newConstant (-10)
    let denominator ← newConstant 3
    let target ← newIntVar (.ofInterval (-20) 20)
    let _ ← addDivisionEquality (.ofIntVar target) (.ofIntVar numerator) (.ofIntVar denominator)
    pure target)
  assertEq resp2.status .optimal "division: expected optimal (-10 / 3)"
  assertEq (resp2.value target2) (-3 : Int64) "division: expected -10 / 3 = -3 (rounds toward zero)"

/-- `target == expr % modulus`. The negative-dividend case pins down that the
target's sign follows `expr`, not `modulus`: `-1 = -7 % 3`, not `2`. -/
def testModulo : IO Unit := do
  let (target1, resp1) ← solve (m := do
    let expr ← newConstant 17
    let modulus ← newConstant 5
    let target ← newIntVar (.ofInterval (-20) 20)
    let _ ← addModuloEquality (.ofIntVar target) (.ofIntVar expr) (.ofIntVar modulus)
    pure target)
  assertEq resp1.status .optimal "modulo: expected optimal (17 % 5)"
  assertEq (resp1.value target1) (2 : Int64) "modulo: expected 17 % 5 = 2"

  let (target2, resp2) ← solve (m := do
    let expr ← newConstant (-7)
    let modulus ← newConstant 3
    let target ← newIntVar (.ofInterval (-20) 20)
    let _ ← addModuloEquality (.ofIntVar target) (.ofIntVar expr) (.ofIntVar modulus)
    pure target)
  assertEq resp2.status .optimal "modulo: expected optimal (-7 % 3)"
  assertEq (resp2.value target2) (-1 : Int64) "modulo: expected -7 % 3 = -1 (sign follows the dividend)"

/-- `target = a * b` for two small int vars. -/
def testMultiplication : IO Unit := do
  let (target, resp) ← solve (m := do
    let a ← newConstant 3
    let b ← newConstant 4
    let target ← newIntVar (.ofInterval 0 100)
    let _ ← addMultiplicationEquality (.ofIntVar target) #[LinearExpr.ofIntVar a, LinearExpr.ofIntVar b]
    pure target)
  assertEq resp.status .optimal "multiplication: expected optimal"
  assertEq (resp.value target) (12 : Int64) "multiplication: expected 3 * 4 = 12"

/-- A small permutation and its known inverse: `vars = [1, 2, 0]` maps
`invVars = [2, 0, 1]`, i.e. `invVars[vars[i]] == i`. -/
def testInverse : IO Unit := do
  let (invVars, resp) ← solve (m := do
    let vars ← #[1, 2, 0].mapM newConstant
    let invVars ← #[(), (), ()].mapM fun _ => newIntVar (.ofInterval 0 2)
    let _ ← addInverseConstraint vars invVars
    pure invVars)
  assertEq resp.status .optimal "inverse: expected optimal"
  assertEq (invVars.map resp.value) #[2, 0, 1] "inverse: expected [2, 0, 1]"

/-- `addBoolXor` over one true literal, one false literal, and one free
literal forces the free literal to make the total count of true literals odd:
with one already true, the free literal must be false. -/
def testBoolXor : IO Unit := do
  let (free, resp) ← solve (m := do
    let t ← BoolVar.ofIntVar <$> newConstant 1
    let f ← BoolVar.ofIntVar <$> newConstant 0
    let free ← newBoolVar
    let _ ← addBoolXor #[t, f, free]
    pure free)
  assertEq resp.status .optimal "boolXor: expected optimal"
  assertEq (resp.solution.getD free.literal.toNat 0) (0 : Int64)
    "boolXor: expected the free literal forced false to keep parity odd"

/-- `target = |expr|`, including a negative input. -/
def testAbsEquality : IO Unit := do
  let (target1, resp1) ← solve (m := do
    let expr ← newConstant (-7)
    let target ← newIntVar (.ofInterval 0 20)
    let _ ← addAbsEquality (.ofIntVar target) (.ofIntVar expr)
    pure target)
  assertEq resp1.status .optimal "absEquality: expected optimal (|-7|)"
  assertEq (resp1.value target1) (7 : Int64) "absEquality: expected |-7| = 7"

  let (target2, resp2) ← solve (m := do
    let expr ← newConstant 5
    let target ← newIntVar (.ofInterval 0 20)
    let _ ← addAbsEquality (.ofIntVar target) (.ofIntVar expr)
    pure target)
  assertEq resp2.status .optimal "absEquality: expected optimal (|5|)"
  assertEq (resp2.value target2) (5 : Int64) "absEquality: expected |5| = 5"

/-- Infeasible model: `x <= 1` and `x >= 5` over a domain that admits both. -/
def testInfeasible : IO Unit := do
  let (_, resp) ← solve (m := do
    let x ← newIntVar (.ofInterval 0 10) "x"
    let _ ← addLessOrEqual x (.const 1)
    let _ ← addGreaterOrEqual x (.const 5)
    pure x)
  assertEq resp.status .infeasible "infeasible: expected infeasible"

/-- `Test/downstream-consumer` is a package that only `require`s cpsat (from
this checkout, via a local path) and builds a normal `lean_exe`, mirroring the
README's "Using cpsat as a dependency" snippet exactly. Lake does not
propagate a package's `weakLinkArgs`/`weakLeancArgs` to a consumer's own
targets, so a downstream package must set them itself; this builds and runs
that fixture end to end as a regression test for the snippet staying correct. -/
def testDownstreamConsumer : IO Unit := do
  let fixtureDir : System.FilePath := "Test/downstream-consumer"
  let build ← IO.Process.output { cmd := "lake", args := #["build"], cwd := some fixtureDir }
  assert (build.exitCode == 0)
    s!"downstream-consumer: `lake build` failed:\n{build.stdout}\n{build.stderr}"
  let run ← IO.Process.output {
    cmd := (fixtureDir / ".lake" / "build" / "bin" / "downstreamConsumer").toString
  }
  assert (run.exitCode == 0) s!"downstream-consumer: executable failed:\n{run.stderr}"
  assertEq run.stdout.trimAscii.copy "rabbits = 8, pheasants = 12"
    "downstream-consumer: unexpected output"

def main : IO Unit := do
  testRabbitsAndPheasants
  testObjective
  testMaximize
  testAllDifferent
  testExactlyOne
  testLinMax
  testElement
  testDivision
  testModulo
  testMultiplication
  testInverse
  testBoolXor
  testAbsEquality
  testInfeasible
  testDownstreamConsumer
  IO.println "All tests passed."
