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

opaque SolveHandle.Pointed : NonemptyType
def SolveHandle := SolveHandle.Pointed.type
instance : Nonempty SolveHandle := SolveHandle.Pointed.property

@[extern "cpsat_solve_stream_start"]
opaque cpsatSolveStreamStart
    (token : @& StopToken) (modelBytes paramsBytes : @& ByteArray) : IO SolveHandle

/-- `IO (isDone, responseBytes)`: blocks until the next update from a streaming solve started
by `cpsatSolveStreamStart` is available. -/
@[extern "cpsat_solve_stream_next"]
opaque cpsatSolveStreamNext (handle : @& SolveHandle) : IO (Bool × ByteArray)

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

/-- One update from a streaming solve: an improving feasible solution found along the way, or
the final response once the search has ended. -/
inductive SolveUpdate where
  | improving (response : CpSolverResponse)
  | done (response : CpSolverResponse)

private def nextUpdate (handle : SolveHandle) : IO SolveUpdate := do
  let (isDone, bytes) ← cpsatSolveStreamNext handle
  let resp ← decodeResponse bytes
  return if isDone then .done resp else .improving resp

private partial def pullUpdates (handle : SolveHandle)
    (onSolution : CpSolverResponse → IO Unit) : IO CpSolverResponse := do
  match ← nextUpdate handle with
  | .improving resp => onSolution resp; pullUpdates handle onSolution
  | .done resp => pure resp

/-- Like `solveInterruptible`, but also delivers every improving feasible solution found along
the way, in order, via `onSolution`, before returning the same final response `solveInterruptible`
would have. `onSolution` runs on the calling task, never on a CP-SAT-internal thread: CP-SAT's own
solution-observer callback runs synchronously from its internal worker threads, which aren't safe
to run Lean code from, so the native shim only ever hands bytes off a thread-safe queue to
whichever thread is actually pulling from it, i.e. this one.

`token` cancels a streaming solve exactly as it does `solveInterruptible`: a caller that only wants
the first solution can call `StopToken.stop` from within `onSolution` (or from another task) once
it has what it needs, and the underlying search winds down promptly, with this returning shortly
after with whatever was found so far as the final response. -/
def solveWithSolutionCallback (params : SolverParameters) (token : StopToken)
    (onSolution : CpSolverResponse → IO Unit) (m : CpModelM α) : IO (α × CpSolverResponse) := do
  let (result, state) := m.run {}
  let modelBytes ← encodeOrPanic "CpModelProto" (Proto.modelStateToProto state)
  let paramsBytes ← encodeOrPanic "SatParameters" (Proto.parametersToProto params)
  let handle ← cpsatSolveStreamStart token modelBytes paramsBytes
  let final ← pullUpdates handle onSolution
  return (result, final)

end Cpsat
