/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native

/-!
# Actual retained original raw-recovery result

A real retained optional-result cell is allocated before the original actual
single recovery. The input still reads the same existing measured values.
All internal scratch is released by that single call; the original output
and every caller context entry remain live.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual final context adds precisely the original retained optional-result shape. -/
def retainedCtx (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  ctx.addRetained key (OutputShape width) fresh

/-- The complete original optional result is read from its actual retained cell. -/
def retainedRead (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    CInputRef (retainedCtx ctx width key fresh) (OutputShape width) :=
  .storage (CStorageRef.retainedHead ctx key (OutputShape width) fresh)

/-- Real result allocation precedes actual preparation, checked inversion and selected recovery. -/
def retainedCircuit (spec : ModulusSpec width)
    (input : CInputRef ctx (.fixedVector (width + width) (.finite 2)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) : Circuit ctx (retainedCtx ctx width key fresh) :=
  .seq (.retain ctx key (OutputShape width) fresh)
    (singleIntoResult spec (input.underRetained key (OutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (OutputShape width) fresh))

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
