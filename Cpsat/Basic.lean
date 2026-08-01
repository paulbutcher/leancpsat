-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Cpsat.Model

/-!
Solver-facing plain data types: parameters going in, response coming out.
Independent of `Cpsat.Proto` (the wire encoding) and `Cpsat.Solver` (the FFI
boundary), so both can depend on this without a cycle.
-/

namespace Cpsat

structure SolverParameters where
  maxTimeInSeconds : Option Float := none
  numWorkers : Option Nat := none
  randomSeed : Option Nat := none
  logSearchProgress : Bool := false
deriving Inhabited

inductive CpSolverStatus where
  | unknown
  | modelInvalid
  | feasible
  | infeasible
  | optimal
deriving Repr, DecidableEq, BEq, Inhabited

structure CpSolverResponse where
  status : CpSolverStatus
  objectiveValue : Float
  bestObjectiveBound : Float
  /-- Indexed by `IntVar.index`. -/
  solution : Array Int64
  wallTime : Float
deriving Inhabited

def CpSolverResponse.value (r : CpSolverResponse) (v : IntVar) : Int64 :=
  r.solution.getD v.index 0

end Cpsat
