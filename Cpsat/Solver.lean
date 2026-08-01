-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Cpsat.Proto

/-!
The FFI boundary: serialize a finished model to `CpModelProto`/`SatParameters`
bytes, hand them to `native/cpsat_shim.cpp`, decode the `CpSolverResponse`
bytes that come back. Everything above this file is plain, ordinary Lean.
-/

namespace Cpsat

@[extern "cpsat_solve"]
opaque cpsatSolve (modelBytes paramsBytes : @& ByteArray) : IO ByteArray

opaque StopToken.Pointed : NonemptyType
def StopToken := StopToken.Pointed.type
instance : Nonempty StopToken := StopToken.Pointed.property

@[extern "cpsat_new_stop_token"]
opaque cpsatNewStopToken : IO StopToken

@[extern "cpsat_stop_token_stop"]
opaque cpsatStopTokenStop (token : @& StopToken) : IO Unit

@[extern "cpsat_solve_interruptible"]
opaque cpsatSolveInterruptible
    (token : @& StopToken) (modelBytes paramsBytes : @& ByteArray) : IO ByteArray

def StopToken.new : IO StopToken := cpsatNewStopToken

def StopToken.stop (t : StopToken) : IO Unit := cpsatStopTokenStop t

private def encodeOrPanic [Protobuf.ProtoMessage α] (label : String) (v : α) : IO ByteArray :=
  match Protobuf.encode v with
  | .ok bytes => pure bytes
  | .error e => throw <| IO.userError s!"internal error encoding {label}: {e}"

private def decodeResponse (bytes : ByteArray) : IO CpSolverResponse :=
  match Protobuf.decodeThe Proto.CpSolverResponseProto bytes with
  | .ok resp => pure (Proto.responseFromProto resp)
  | .error e => throw <| IO.userError s!"internal error decoding CpSolverResponse: {e}"

/-- Run a model-building computation, then solve it. -/
def solve (params : SolverParameters := {}) (m : CpModelM α) : IO (α × CpSolverResponse) := do
  let (result, state) := m.run {}
  let modelBytes ← encodeOrPanic "CpModelProto" (Proto.modelStateToProto state)
  let paramsBytes ← encodeOrPanic "SatParameters" (Proto.parametersToProto params)
  let responseBytes ← cpsatSolve modelBytes paramsBytes
  return (result, ← decodeResponse responseBytes)

/-- Like `solve`, but cooperatively cancellable via `token`, e.g. from another
Lean task/thread calling `StopToken.stop`. -/
def solveInterruptible (params : SolverParameters) (token : StopToken)
    (m : CpModelM α) : IO (α × CpSolverResponse) := do
  let (result, state) := m.run {}
  let modelBytes ← encodeOrPanic "CpModelProto" (Proto.modelStateToProto state)
  let paramsBytes ← encodeOrPanic "SatParameters" (Proto.parametersToProto params)
  let responseBytes ← cpsatSolveInterruptible token modelBytes paramsBytes
  return (result, ← decodeResponse responseBytes)

end Cpsat
