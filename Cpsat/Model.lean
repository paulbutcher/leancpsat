-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

/-!
Pure, FFI-free CP-SAT model builder. No protobuf or solver knowledge lives
here; `Cpsat.Proto` turns a finished `ModelState` into wire bytes.
-/

namespace Cpsat

/-- A closed-interval domain for an integer variable: a sorted, disjoint union
of inclusive `[lo, hi]` ranges. -/
structure Domain where
  intervals : Array (Int64 × Int64)
deriving Repr, Inhabited

namespace Domain

def ofInterval (lo hi : Int64) : Domain := ⟨#[(lo, hi)]⟩
def single (v : Int64) : Domain := ofInterval v v

/-- Every value except `v`. -/
def excluding (v : Int64) : Domain :=
  ⟨#[(Int64.minValue, v - 1), (v + 1, Int64.maxValue)]⟩

end Domain

/-- An index into the model's variable array. -/
structure IntVar where
  index : Nat
deriving Repr, DecidableEq, Inhabited

/-- A boolean literal: a reference to a 0/1-domain variable, or its negation
(mirroring CP-SAT's own literal encoding, where variables double as their own
Boolean view). -/
structure BoolVar where
  literal : Int
deriving Repr, DecidableEq, Inhabited

namespace BoolVar

def ofIntVar (v : IntVar) : BoolVar := ⟨(v.index : Int)⟩
def not (b : BoolVar) : BoolVar := ⟨-b.literal - 1⟩

end BoolVar

/-- An affine combination of integer variables plus a constant. -/
structure LinearExpr where
  terms : Array (IntVar × Int64) := #[]
  constant : Int64 := 0
deriving Repr, Inhabited

namespace LinearExpr

def const (c : Int64) : LinearExpr := { constant := c }
def ofIntVar (v : IntVar) : LinearExpr := { terms := #[(v, 1)] }

instance : Coe IntVar LinearExpr := ⟨ofIntVar⟩

instance : Neg LinearExpr where
  neg e := { terms := e.terms.map fun (v, c) => (v, -c), constant := -e.constant }

instance : Add LinearExpr where
  add a b := { terms := a.terms ++ b.terms, constant := a.constant + b.constant }

instance : Sub LinearExpr where
  sub a b := a + (-b)

instance : HAdd IntVar IntVar LinearExpr where
  hAdd a b := ofIntVar a + ofIntVar b

instance : HAdd LinearExpr IntVar LinearExpr where
  hAdd a b := a + ofIntVar b

instance : HAdd IntVar LinearExpr LinearExpr where
  hAdd a b := ofIntVar a + b

instance : HMul Int64 IntVar LinearExpr where
  hMul c v := { terms := #[(v, c)] }

instance : HMul Int64 LinearExpr LinearExpr where
  hMul c e := { terms := e.terms.map fun (v, coeff) => (v, c * coeff), constant := c * e.constant }

end LinearExpr

/-- An index into the model's constraint array. -/
structure Constraint where
  index : Nat
deriving Repr, DecidableEq, Inhabited

/-- The constraint kinds currently supported. Each maps to exactly one CP-SAT
`ConstraintProto` oneof case; CP-SAT has several more, each addable the same
way (a case here, a message in `Cpsat.Proto`, an `addX` function). -/
inductive ConstraintKind where
  | linear (expr : LinearExpr) (domain : Domain)
  | allDifferent (vars : Array IntVar)
  | boolOr (lits : Array BoolVar)
  | boolAnd (lits : Array BoolVar)
  | atMostOne (lits : Array BoolVar)
  | exactlyOne (lits : Array BoolVar)
  | linMax (target : LinearExpr) (exprs : Array LinearExpr)
  | element (index : LinearExpr) (exprs : Array LinearExpr) (target : LinearExpr)
  | intDiv (target numerator denominator : LinearExpr)
  | intMod (target expr modulus : LinearExpr)
  | intProd (target : LinearExpr) (factors : Array LinearExpr)
  | inverse (vars invVars : Array IntVar)
  | boolXor (lits : Array BoolVar)
deriving Repr, Inhabited

structure ConstraintData where
  kind : ConstraintKind
  enforcementLiterals : Array BoolVar := #[]
  name : String := ""
deriving Inhabited

structure ModelState where
  name : String := ""
  varDomains : Array Domain := #[]
  varNames : Array String := #[]
  constraints : Array ConstraintData := #[]
  /-- `some (expr, maximize?)`. -/
  objective : Option (LinearExpr × Bool) := none
  /-- Literals tracked for infeasibility explanation; see `markAssumption`. -/
  assumptions : Array BoolVar := #[]
deriving Inhabited

/-- Model-building is a plain state computation; no FFI is involved until
`Cpsat.solve` serializes the finished `ModelState`. -/
abbrev CpModelM := StateM ModelState

def setModelName (name : String) : CpModelM Unit :=
  modify fun s => { s with name }

def newIntVar (domain : Domain) (name : String := "") : CpModelM IntVar := do
  let s ← get
  let idx := s.varDomains.size
  set { s with varDomains := s.varDomains.push domain, varNames := s.varNames.push name }
  return ⟨idx⟩

def newBoolVar (name : String := "") : CpModelM BoolVar :=
  BoolVar.ofIntVar <$> newIntVar (.ofInterval 0 1) name

def newConstant (value : Int64) : CpModelM IntVar :=
  newIntVar (.single value)

def addConstraint (kind : ConstraintKind) (enforcementLiterals : Array BoolVar := #[])
    (name : String := "") : CpModelM Constraint := do
  let s ← get
  let idx := s.constraints.size
  set { s with constraints := s.constraints.push { kind, enforcementLiterals, name } }
  return ⟨idx⟩

def addLinearConstraint (expr : LinearExpr) (domain : Domain) : CpModelM Constraint :=
  addConstraint (.linear expr domain)

def addEquality (lhs rhs : LinearExpr) : CpModelM Constraint :=
  addLinearConstraint (lhs - rhs) (.single 0)

def addLessOrEqual (lhs rhs : LinearExpr) : CpModelM Constraint :=
  addLinearConstraint (lhs - rhs) (.ofInterval Int64.minValue 0)

def addGreaterOrEqual (lhs rhs : LinearExpr) : CpModelM Constraint :=
  addLinearConstraint (lhs - rhs) (.ofInterval 0 Int64.maxValue)

def addNotEqual (lhs rhs : LinearExpr) : CpModelM Constraint :=
  addLinearConstraint (lhs - rhs) (.excluding 0)

def addAllDifferent (vars : Array IntVar) : CpModelM Constraint :=
  addConstraint (.allDifferent vars)

def addBoolOr (lits : Array BoolVar) : CpModelM Constraint :=
  addConstraint (.boolOr lits)

def addBoolAnd (lits : Array BoolVar) : CpModelM Constraint :=
  addConstraint (.boolAnd lits)

def addAtMostOne (lits : Array BoolVar) : CpModelM Constraint :=
  addConstraint (.atMostOne lits)

def addExactlyOne (lits : Array BoolVar) : CpModelM Constraint :=
  addConstraint (.exactlyOne lits)

def addMaxEquality (target : LinearExpr) (exprs : Array LinearExpr) : CpModelM Constraint :=
  addConstraint (.linMax target exprs)

/-- CP-SAT has no `lin_min` constraint kind; the C++ builder itself derives
`AddMinEquality` from `AddMaxEquality` by negating the target and every
expression (`cp_model.cc`), and this mirrors that exactly. -/
def addMinEquality (target : LinearExpr) (exprs : Array LinearExpr) : CpModelM Constraint :=
  addMaxEquality (-target) (exprs.map (-·))

/-- `exprs[index] == target`. `exprs` entries can be arbitrary linear
expressions, not just variables, so a constant array of values (the "array of
int64 values" C++ overload) is just `exprs.map .const`. -/
def addElement (index : LinearExpr) (exprs : Array LinearExpr) (target : LinearExpr) :
    CpModelM Constraint :=
  addConstraint (.element index exprs target)

/-- `target == numerator / denominator`, rounded towards zero (so
`-3 = -10 / 3`, not `-4`). The model is invalid if `denominator`'s domain can
be zero. -/
def addDivisionEquality (target numerator denominator : LinearExpr) : CpModelM Constraint :=
  addConstraint (.intDiv target numerator denominator)

/-- `target == expr % modulus`. `modulus`'s domain must be strictly positive.
The sign of `target` matches the sign of `expr` (so `-1 = -7 % 3`, not `2`). -/
def addModuloEquality (target expr modulus : LinearExpr) : CpModelM Constraint :=
  addConstraint (.intMod target expr modulus)

/-- `target` equals the product of every element of `factors`. -/
def addMultiplicationEquality (target : LinearExpr) (factors : Array LinearExpr) :
    CpModelM Constraint :=
  addConstraint (.intProd target factors)

/-- `vars`/`invVars` are inverse permutations of each other:
`invVars[vars[i]] == i` for every `i`. -/
def addInverseConstraint (vars invVars : Array IntVar) : CpModelM Constraint :=
  addConstraint (.inverse vars invVars)

/-- Forces an odd number of `lits` to be true. -/
def addBoolXor (lits : Array BoolVar) : CpModelM Constraint :=
  addConstraint (.boolXor lits)

/-- `target == |expr|`. CP-SAT has no `abs_equality` oneof case; the C++
builder itself lowers this to `lin_max(target, {expr, -expr})`
(`cp_model.cc`), and this mirrors that exactly, same as `addMinEquality`. -/
def addAbsEquality (target expr : LinearExpr) : CpModelM Constraint :=
  addMaxEquality target #[expr, -expr]

/-- `a → b`, encoded as `¬a ∨ b`. -/
def addImplication (a b : BoolVar) : CpModelM Constraint :=
  addBoolOr #[a.not, b]

def Constraint.onlyEnforceIf (c : Constraint) (lits : Array BoolVar) : CpModelM Unit :=
  modify fun s =>
    match s.constraints[c.index]? with
    | some cd =>
      { s with
        constraints :=
          s.constraints.set! c.index { cd with enforcementLiterals := cd.enforcementLiterals ++ lits } }
    | none => s

def minimize (expr : LinearExpr) : CpModelM Unit :=
  modify fun s => { s with objective := some (expr, false) }

def maximize (expr : LinearExpr) : CpModelM Unit :=
  modify fun s => { s with objective := some (expr, true) }

/-- Tracks `b` as an assumption: if the solve comes back infeasible,
`CpSolverResponse.sufficientAssumptionsForInfeasibility` will report a subset
of the model's marked assumptions that's jointly sufficient to prove
infeasibility. -/
def markAssumption (b : BoolVar) : CpModelM Unit :=
  modify fun s => { s with assumptions := s.assumptions.push b }

def markAssumptions (bs : Array BoolVar) : CpModelM Unit :=
  modify fun s => { s with assumptions := s.assumptions ++ bs }

end Cpsat
