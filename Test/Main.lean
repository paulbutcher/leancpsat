-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

import Cpsat
-- The theorems below unfold definitions whose bodies the public interface does not expose.
import all Cpsat.Model
import all Cpsat.Proto

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

/-- Two conflicting constraints, each gated behind its own assumption
literal: `x <= 1` behind `aLE`, `x >= 5` behind `aGE`. Marking both as
assumptions (instead of enforcing them unconditionally) lets the infeasible
solve report which assumptions were jointly responsible, rather than just
that the model as a whole is infeasible. Since only these two literals are
marked, and dropping either one leaves the model feasible, the sufficient
core CP-SAT reports must be exactly both, regardless of how many workers
solve it. -/
def testAssumptions : IO Unit := do
  let ((aLE, aGE), resp) ← solve (m := do
    let x ← newIntVar (.ofInterval 0 10) "x"
    let aLE ← newBoolVar "aLE"
    let aGE ← newBoolVar "aGE"
    let le ← addLessOrEqual x (.const 1)
    le.onlyEnforceIf #[aLE]
    let ge ← addGreaterOrEqual x (.const 5)
    ge.onlyEnforceIf #[aGE]
    markAssumptions #[aLE, aGE]
    pure (aLE, aGE))
  assertEq resp.status .infeasible "assumptions: expected infeasible"
  let core := resp.sufficientAssumptionsForInfeasibility
  assert (core.any (·.literal == aLE.literal)) "assumptions: expected aLE in the sufficient core"
  assert (core.any (·.literal == aGE.literal)) "assumptions: expected aGE in the sufficient core"
  assertEq core.size 2 "assumptions: expected exactly the two marked assumptions in the core"

/-- A 0/1 knapsack (maximize total value of selected items subject to a weight capacity), sized
and varied enough that CP-SAT, restricted to a single worker for a deterministic sequence of
incumbents, finds more than one feasible solution en route to the optimum. -/
def knapsack : CpModelM Unit := do
  let n := 30
  let items ← (List.range n).toArray.mapM fun _ => newIntVar (.ofInterval 0 1)
  let weight (i : Nat) : Int64 := Int64.ofNat ((i % 7) + 3)
  let value (i : Nat) : Int64 := Int64.ofNat (((i * 5) % 13) + 1)
  let mut weightExpr := LinearExpr.const 0
  let mut valueExpr := LinearExpr.const 0
  let mut capacity : Int64 := 0
  for i in [0:n] do
    weightExpr := weightExpr + weight i * items[i]!
    valueExpr := valueExpr + value i * items[i]!
    capacity := capacity + weight i
  let _ ← addLessOrEqual weightExpr (.const (capacity * 6 / 10))
  maximize valueExpr

/-- Streaming solve of `knapsack`: every `onSolution` callback should fire before the final
response, in increasing objective order (CP-SAT only calls it on improving solutions), and the
final response should agree with what `solveInterruptible` finds for the same model. -/
def testStreamingSolve : IO Unit := do
  let params : SolverParameters := { numWorkers := some 1 }
  let objectivesRef ← IO.mkRef (#[] : Array Float)
  let ((), streamResp) ← solveWithSolutionCallback params (← StopToken.new)
    (fun resp => objectivesRef.modify (·.push resp.objectiveValue)) knapsack
  let objectives ← objectivesRef.get
  assert (objectives.size ≥ 1) "streamingSolve: expected at least one onSolution callback"
  for i in [1:objectives.size] do
    assert (objectives[i]! ≥ objectives[i - 1]!)
      "streamingSolve: expected each callback's objective to be at least as good as the previous"
  assertEq streamResp.status .optimal "streamingSolve: expected optimal"
  assertEq objectives.back! streamResp.objectiveValue
    "streamingSolve: last callback should report the same objective as the final response"

  let (_, plainResp) ← solveInterruptible params (← StopToken.new) knapsack
  assertEq plainResp.status streamResp.status
    "streamingSolve: status should match solveInterruptible"
  assertEq plainResp.objectiveValue streamResp.objectiveValue
    "streamingSolve: objective should match solveInterruptible"

/-- Calling `StopToken.stop` from within `onSolution`, after the first callback, should still let
`solveWithSolutionCallback` return promptly (rather than run `knapsack` to completion), mirroring
`solveInterruptible`'s cancellation contract. -/
def testStreamingSolveStop : IO Unit := do
  let params : SolverParameters := { numWorkers := some 1 }
  let token ← StopToken.new
  let stoppedRef ← IO.mkRef false
  let start ← IO.monoMsNow
  let ((), resp) ← solveWithSolutionCallback params token
    (fun _resp => do
      unless ← stoppedRef.get do
        stoppedRef.set true
        token.stop) knapsack
  let elapsed ← IO.monoMsNow
  assert (elapsed - start < 10000)
    "streamingSolveStop: expected StopToken.stop to make the call return promptly"
  assert (resp.status == .optimal || resp.status == .feasible)
    "streamingSolveStop: expected a feasible or optimal response after stopping early"

/-- `maximize 3x + 2y` subject to `x + y ≤ 4` over `x ∈ [0, 2]`, `y ∈ [0, 10]`,
plus `y ≤ 1` enforced by `b`: a unique optimum at `b` false, `x = 2`, `y = 2`,
objective 10. `hint` runs last, so each caller offers a different starting point
(or none at all) for one and the same model. -/
def hintedModel (hint : IntVar → IntVar → BoolVar → CpModelM Unit) :
    CpModelM (IntVar × IntVar × BoolVar) := do
  let x ← newIntVar (.ofInterval 0 2) "x"
  let y ← newIntVar (.ofInterval 0 10) "y"
  let b ← newBoolVar "b"
  let _ ← addLessOrEqual (x + y) (.const 4)
  let capped ← addLessOrEqual y (.const 1)
  capped.onlyEnforceIf #[b]
  maximize ((3 : Int64) * x + (2 : Int64) * y)
  hint x y b
  pure (x, y, b)

/-- A hint is advice, never a constraint, so no hint may change the answer:
naming the optimum, naming a feasible non-optimal point, and naming values no
solution has (indeed that no variable's domain even contains) must all leave the
same unique optimum reached. -/
def testSolutionHint : IO Unit := do
  let expectOptimum (label : String) (hint : IntVar → IntVar → BoolVar → CpModelM Unit) : IO Unit := do
    let ((x, y, b), resp) ← solve (m := hintedModel hint)
    assertEq resp.status .optimal s!"solutionHint: expected optimal ({label})"
    assertEq resp.objectiveValue (10.0 : Float) s!"solutionHint: expected objective 10 ({label})"
    assertEq (resp.value x) (2 : Int64) s!"solutionHint: expected x = 2 ({label})"
    assertEq (resp.value y) (2 : Int64) s!"solutionHint: expected y = 2 ({label})"
    assertEq (resp.solution.getD b.literal.toNat 0) (0 : Int64)
      s!"solutionHint: expected b false ({label})"

  expectOptimum "unhinted" fun _ _ _ => pure ()

  expectOptimum "the optimum" fun x y b => do
    addSolutionHint #[(x, 2), (y, 2)]
    addBoolSolutionHint #[(b, false)]

  -- `b.not` false is `b` true, so this also exercises `BoolVar.hint`'s
  -- negated-literal case against the solver rather than only in the abstract.
  expectOptimum "a feasible non-optimal point" fun x y b => do
    addSolutionHint #[(x, 2), (y, 1)]
    addBoolSolutionHint #[(b.not, false)]

  expectOptimum "values outside every domain" fun x y b => do
    addSolutionHint #[(x, 9), (y, -3)]
    addBoolSolutionHint #[(b, true)]

/-- CP-SAT's validator rejects a hint naming the same variable twice, which
makes this the positive check that the hint actually arrives in
`CpModelProto.solution_hint`: a field that went unwritten, or landed on a number
CP-SAT doesn't read, would leave this model perfectly valid. -/
def testDuplicateSolutionHint : IO Unit := do
  let (_, resp) ← solve (m := hintedModel fun x _ _ => addSolutionHint #[(x, 0), (x, 1)])
  assertEq resp.status .modelInvalid "duplicateSolutionHint: expected the model to be rejected"
  assert ((resp.solutionInfo.splitOn "solution hint").length > 1)
    s!"duplicateSolutionHint: expected solutionInfo to name the hint, got: {resp.solutionInfo}"

/-- `solutionInfo` names the subsolver whose solution won, so a solve that
actually finds one must fill it in. -/
def testSolutionInfo : IO Unit := do
  let ((), resp) ← solve (m := knapsack)
  assertEq resp.status .optimal "solutionInfo: expected optimal"
  assert (!resp.solutionInfo.isEmpty) "solutionInfo: expected the winning subsolver to be named"

/-- Hinting `b` to `value` and hinting `b.not` to `!value` are the same
instruction, so they must resolve to the same `(variable, value)` pair. -/
theorem boolVarHintNot (b : BoolVar) (value : Bool) : b.hint value = b.not.hint (!value) := by
  unfold BoolVar.hint BoolVar.not
  dsimp only
  rcases Int.lt_or_le b.literal 0 with h | h
  · rw [if_pos h, if_neg (show ¬ (-b.literal - 1 < 0) by omega)]
    cases value <;> rfl
  · rw [if_neg (show ¬ (b.literal < 0) by omega), if_pos (show -b.literal - 1 < 0 by omega),
      show -(-b.literal - 1) - 1 = b.literal by omega]
    cases value <;> rfl

/-- Absent and present-but-empty are different messages on the wire, and only
absent means "no hint offered", so a hintless model must not emit the field at
all. Invisible in the Lean value, hence worth pinning here. -/
theorem hintlessModelEmitsNoHint (s : ModelState) (h : s.solutionHint.isEmpty) :
    (Proto.modelStateToProto s).solution_hint = none := by
  simp [Proto.modelStateToProto, h]

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

public def main : IO Unit := do
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
  testAssumptions
  testSolutionHint
  testDuplicateSolutionHint
  testSolutionInfo
  testStreamingSolve
  testStreamingSolveStop
  testDownstreamConsumer
  IO.println "All tests passed."
