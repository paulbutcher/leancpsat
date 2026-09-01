-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.

module

public import Protobuf
public import Cpsat.Model
public import Cpsat.Basic

/-!
Wire format layer: message shapes declared by hand against
[Lean-zh/protobuf](https://github.com/Lean-zh/protobuf)'s internal notation
(no `protoc`, no `.proto` sources), plus conversions between the generated
message types and `Cpsat.Model`'s builder types. Field numbers are cited
against the vendored `or-tools/ortools/sat/cp_model.proto` and
`or-tools/ortools/sat/sat_parameters.proto`.

Only the subset of `ConstraintProto`'s `oneof constraint` needed by the
constraint kinds currently supported is declared; the wire format tolerates a
message that doesn't know about every oneof case, so declaring more of them
later never requires touching already-declared fields.
-/

open scoped Protobuf.Notation

public section

namespace Cpsat.Proto

message LinearExpressionProto {
  repeated int32 vars = 1 [packed = true];
  repeated int64 coeffs = 2 [packed = true];
  int64 offset = 3;
}

message BoolArgumentProto {
  repeated int32 literals = 1 [packed = true];
}

message LinearConstraintProto {
  repeated int32 vars = 1 [packed = true];
  repeated int64 coeffs = 2 [packed = true];
  repeated int64 domain = 3 [packed = true];
}

message AllDifferentConstraintProto {
  repeated LinearExpressionProto exprs = 1;
}

-- Shared by `lin_max`, `int_div`, `int_mod`, and `int_prod` in the real
-- `ConstraintProto` oneof: a target expression plus a list of operands.
message LinearArgumentProto {
  LinearExpressionProto target = 1;
  repeated LinearExpressionProto exprs = 2;
}

-- Field numbers 1-3 (`index`/`target`/`vars`) are a legacy plain-int32 shape
-- the real C++ builder no longer populates; only the `linear_*`/`exprs` shape
-- it actually writes is declared here.
message ElementConstraintProto {
  LinearExpressionProto linear_index = 4;
  LinearExpressionProto linear_target = 5;
  repeated LinearExpressionProto exprs = 6;
}

-- Unlike `ElementConstraintProto`, the real C++ builder's only
-- `AddInverseConstraint` overload writes the legacy plain-int32
-- `f_direct`/`f_inverse` fields, not the newer `f_expr_direct`/
-- `f_expr_inverse` (`LinearExpressionProto`) ones - so those are what's
-- declared here.
message InverseConstraintProto {
  repeated int32 f_direct = 1 [packed = true];
  repeated int32 f_inverse = 2 [packed = true];
}

oneof ConstraintKindProto {
  BoolArgumentProto bool_or = 3;
  BoolArgumentProto bool_and = 4;
  BoolArgumentProto bool_xor = 5;
  BoolArgumentProto at_most_one = 26;
  BoolArgumentProto exactly_one = 29;
  LinearConstraintProto linear = 12;
  AllDifferentConstraintProto all_diff = 13;
  ElementConstraintProto element = 14;
  InverseConstraintProto inverse = 18;
  LinearArgumentProto int_div = 7;
  LinearArgumentProto int_mod = 8;
  LinearArgumentProto int_prod = 11;
  LinearArgumentProto lin_max = 27;
}

message ConstraintProto {
  string name = 1;
  repeated int32 enforcement_literal = 2 [packed = true];
  ConstraintKindProto constraint = 0;
}

message IntegerVariableProto {
  string name = 1;
  repeated int64 domain = 2 [packed = true];
}

message CpObjectiveProto {
  repeated int32 vars = 1 [packed = true];
  repeated int64 coeffs = 4 [packed = true];
  double offset = 2;
  double scaling_factor = 3;
}

message PartialVariableAssignmentProto {
  repeated int32 vars = 1 [packed = true];
  repeated int64 values = 2 [packed = true];
}

message CpModelProto {
  string name = 1;
  repeated IntegerVariableProto variables = 2;
  repeated ConstraintProto constraints = 3;
  CpObjectiveProto objective = 4;
  PartialVariableAssignmentProto solution_hint = 6;
  repeated int32 assumptions = 7 [packed = true];
}

enum CpSolverStatusProto {
  UNKNOWN = 0;
  MODEL_INVALID = 1;
  FEASIBLE = 2;
  INFEASIBLE = 3;
  OPTIMAL = 4;
}

message CpSolverResponseProto {
  CpSolverStatusProto status = 1;
  repeated int64 solution = 2 [packed = true];
  double objective_value = 3;
  double best_objective_bound = 4;
  double wall_time = 15;
  string solution_info = 20;
  repeated int32 sufficient_assumptions_for_infeasibility = 23 [packed = true];
}

message SatParametersProto {
  optional double max_time_in_seconds = 36;
  optional int32 random_seed = 31;
  optional bool log_search_progress = 41;
  optional int32 num_workers = 206;
}

private def varRef (v : IntVar) : Int32 := Int32.ofInt (Int.ofNat v.index)

private def litRef (b : BoolVar) : Int32 := Int32.ofInt b.literal

/-- Clamp to the `Int64` range instead of wrapping, so shifting a domain that
touches `Int64.minValue`/`Int64.maxValue` (CP-SAT's "unbounded" sentinels)
keeps them at the extreme rather than overflowing past them. -/
private def clampToInt64 (x : Int) : Int64 :=
  if x < Int64.minValue.toInt then Int64.minValue
  else if x > Int64.maxValue.toInt then Int64.maxValue
  else Int64.ofInt x

/-- `LinearConstraintProto`'s domain has no offset field, unlike
`LinearExpr`. Shift the domain by `-constant` so `sum(coeffs*vars) + constant
∈ domain` becomes the equivalent `sum(coeffs*vars) ∈ domain - constant`. -/
private def shiftDomain (d : Domain) (constant : Int64) : Domain :=
  ⟨d.intervals.map fun (lo, hi) =>
    (clampToInt64 (lo.toInt - constant.toInt), clampToInt64 (hi.toInt - constant.toInt))⟩

private def domainToFlatArray (d : Domain) : Array Int64 :=
  d.intervals.flatMap fun (lo, hi) => #[lo, hi]

private def linearExprToProto (e : LinearExpr) : LinearExpressionProto :=
  { vars := e.terms.map (varRef ·.1), coeffs := e.terms.map (·.2), offset := e.constant }

private def constraintKindToProto : ConstraintKind → ConstraintKindProto
  | .linear expr domain =>
    .linear {
      vars := expr.terms.map (varRef ·.1)
      coeffs := expr.terms.map (·.2)
      domain := domainToFlatArray (shiftDomain domain expr.constant)
    }
  | .allDifferent vars => .all_diff { exprs := vars.map fun v => linearExprToProto (.ofIntVar v) }
  | .boolOr lits => .bool_or { literals := lits.map litRef }
  | .boolAnd lits => .bool_and { literals := lits.map litRef }
  | .atMostOne lits => .at_most_one { literals := lits.map litRef }
  | .exactlyOne lits => .exactly_one { literals := lits.map litRef }
  | .linMax target exprs =>
    .lin_max { target := linearExprToProto target, exprs := exprs.map linearExprToProto }
  | .element index exprs target =>
    .element {
      linear_index := some (linearExprToProto index)
      linear_target := some (linearExprToProto target)
      exprs := exprs.map linearExprToProto
    }
  | .intDiv target numerator denominator =>
    .int_div {
      target := some (linearExprToProto target)
      exprs := #[linearExprToProto numerator, linearExprToProto denominator]
    }
  | .intMod target expr modulus =>
    .int_mod {
      target := some (linearExprToProto target)
      exprs := #[linearExprToProto expr, linearExprToProto modulus]
    }
  | .intProd target factors =>
    .int_prod { target := some (linearExprToProto target), exprs := factors.map linearExprToProto }
  | .inverse vars invVars => .inverse { f_direct := vars.map varRef, f_inverse := invVars.map varRef }
  | .boolXor lits => .bool_xor { literals := lits.map litRef }

private def constraintDataToProto (cd : ConstraintData) : ConstraintProto :=
  {
    name := cd.name
    enforcement_literal := cd.enforcementLiterals.map litRef
    constraint := some (constraintKindToProto cd.kind)
  }

private def objectiveToProto (expr : LinearExpr) (maximize : Bool) : CpObjectiveProto :=
  let vars := expr.terms.map (varRef ·.1)
  let coeffs := expr.terms.map (·.2)
  if maximize then
    { vars, coeffs := coeffs.map (-·), offset := -(Float.ofInt expr.constant.toInt),
      scaling_factor := -1.0 }
  else
    { vars, coeffs, offset := Float.ofInt expr.constant.toInt, scaling_factor := 1.0 }

def modelStateToProto (s : ModelState) : CpModelProto :=
  {
    name := s.name
    variables :=
      (s.varDomains.zip s.varNames).map fun (d, n) => { name := n, domain := domainToFlatArray d }
    constraints := s.constraints.map constraintDataToProto
    objective := s.objective.map fun (expr, maximize) => objectiveToProto expr maximize
    -- A present-but-empty `PartialVariableAssignment` is not the same thing as
    -- an absent one, so a hintless model must omit the field entirely.
    solution_hint :=
      if s.solutionHint.isEmpty then none
      else some {
        vars := s.solutionHint.map (varRef ·.1)
        values := s.solutionHint.map (·.2)
      }
    assumptions := s.assumptions.map litRef
  }

def parametersToProto (p : SolverParameters) : SatParametersProto :=
  {
    max_time_in_seconds := p.maxTimeInSeconds
    random_seed := p.randomSeed.map fun n => Int32.ofInt (Int.ofNat n)
    log_search_progress := if p.logSearchProgress then some true else none
    num_workers := p.numWorkers.map fun n => Int32.ofInt (Int.ofNat n)
  }

def statusFromProto : CpSolverStatusProto → CpSolverStatus
  | .UNKNOWN => .unknown
  | .MODEL_INVALID => .modelInvalid
  | .FEASIBLE => .feasible
  | .INFEASIBLE => .infeasible
  | .OPTIMAL => .optimal
  | _ => .unknown

def responseFromProto (r : CpSolverResponseProto) : CpSolverResponse :=
  {
    status := statusFromProto r.status
    objectiveValue := r.objective_value
    bestObjectiveBound := r.best_objective_bound
    solution := r.solution
    wallTime := r.wall_time
    solutionInfo := r.solution_info
    sufficientAssumptionsForInfeasibility :=
      r.sufficient_assumptions_for_infeasibility.map fun lit => ⟨lit.toInt⟩
  }

end Cpsat.Proto
