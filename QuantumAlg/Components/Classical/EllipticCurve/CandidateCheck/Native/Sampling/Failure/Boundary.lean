/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Initialization

/-!
# Actual final-output failure mass

The real final option-pack reports no result precisely when the existing
accepted bit is false, regardless of the selected word. The event reads the
same final batchResultRead and preserves every complete reference block.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem retainedStep_indicator_weight (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) {input output : CShape}
    (op : ClassicalOp input output
      (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (condition : Store (ctx.addRetained key shape fresh) → Prop) [DecidablePred condition] :
    ((Circuit.retainedStep ctx key shape fresh op).execute Reference state).effectWeight
        (fun entry => if condition entry.1 then
          Effect.one ((ctx.addRetained key shape fresh).register.prod Reference)
        else Effect.zero ((ctx.addRetained key shape fresh).register.prod Reference)) =
      state.effectWeight (fun entry =>
        if condition ((entry.1.pushRetained key shape fresh).applyOp op) then
          Effect.one (ctx.register.prod Reference)
        else Effect.zero (ctx.register.prod Reference)) := by
  rw [Circuit.execute_retainedStep]
  let update : Store ctx × H → Store (ctx.addRetained key shape fresh) × (H × (Unit × Unit)) :=
    fun entry => ((entry.1.pushRetained key shape fresh).applyOp op, (entry.2, ((), ())))
  exact mapped_indicator_weight _ state update (fun entry => condition entry.1)

private theorem packOption_none_iff {shape : CShape}
    (tag : CShape.Value .bit) (value : CShape.Value shape) :
    CShape.packOption (.product tag value) = .optionNone ↔ tag.toBool = false := by
  cases tag with
  | bit flag => cases flag <;> simp [CShape.packOption, CShape.Value.toBool]

private theorem option_none_weight {shape : CShape} {R : Register}
    (state : DensityOperator R) (tag : CShape.Value .bit) (value : CShape.Value shape)
    (observed : CShape.Value (.option shape))
    (same : observed = CShape.packOption (.product tag value)) :
    (if observed = .optionNone then Effect.one R else Effect.zero R).weight state =
      (if tag.toBool = false then Effect.one R else Effect.zero R).weight state := by
  simp only [same, packOption_none_iff]

/-- The actual final optional output is absent exactly with the incoming failure mass. -/
theorem packBatchResult_none_weight (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) :
    ((packBatchResult ctx width scalarWidth).execute Reference state).effectWeight
        (fun entry => if entry.1.read (batchResultRead ctx width scalarWidth) = .optionNone then
          Effect.one ((batchResultCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((batchResultCtx ctx width scalarWidth).register.prod Reference)) =
      state.effectWeight (fun entry => if (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  have weighted := retainedStep_indicator_weight
    (persistentCtx ctx width scalarWidth).canonicalFreshKey (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (batchResultOp ctx width scalarWidth) state
    (fun store => store.read (batchResultRead ctx width scalarWidth) = .optionNone)
  refine weighted.trans ?_
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro entry _
  dsimp only
  exact option_none_weight (state.block entry)
    (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
    (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) _
    (packBatchResultStep_output ctx width scalarWidth entry.1)


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
