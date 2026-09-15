/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State

/-!
# Actual retained GF(2) recovery result

The original optional result is genuinely retained before all seven original
workspace allocations. The actual complete recovery reads the same original
sample input. All internal cells are released after the real packOption;
only the result cell and every original caller-context entry remain live.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The actual final context adds exactly the original optional-result encoding. -/
def retainedCtx (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  ctx.addRetained key (.option (.unsignedWord width)) fresh

/-- The final optional value is read from its actual retained storage cell. -/
def retainedRead (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    CInputRef (retainedCtx ctx width key fresh) (.option (.unsignedWord width)) :=
  .storage (CStorageRef.retainedHead ctx key (.option (.unsignedWord width)) fresh)

/-- Real result retention precedes all actual recovery scopes and original instructions. -/
def retainedCircuit (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) : Circuit ctx (retainedCtx ctx width key fresh) :=
  .seq (.retain ctx key (.option (.unsignedWord width)) fresh)
    (withState (input.underRetained key (.option (.unsignedWord width)) fresh)
      (CWriteRef.retainedHead ctx key (.option (.unsignedWord width)) fresh))

end QuantumAlg.ClassicalRoutines.GF2.Native
