-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
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
