/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# An accepted first value survives the actual sampling loop and final packing

The original chronological loop reuses its existing persistent cells.
Every actual sampling and recovery step preserves an already accepted word.
The final retained option is therefore that same word, including for zero
further attempts. These support statements retain the complete execution
State, Reference and history and require no condition on later samples.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

omit [BitWord.Selected model] in
private theorem preservesStore_forRange (count : Nat)
    (body : Fin count → Circuit model ctx ctx)
    (predicate : Store ctx → Prop) (keeps : ∀ index, PreservesStore (body index) predicate) :
    PreservesStore (Circuit.forRange count body) predicate := by
  induction count with
  | zero =>
      unfold PreservesStore
      intro Reference H _ state holds result positive
      change 0 < (((Circuit.id (model := model) ctx).execute Reference state).block
        result).mass at positive
      rw [Circuit.execute_id_mapClassical] at positive
      obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
      rw [← equality]
      exact holds original present
  | succ count ih =>
      exact preservesStore_seq (body 0)
        (Circuit.forRange count (fun index => body index.succ)) predicate
        (@keeps 0) (ih (fun index => body index.succ) (fun index => @keeps index.succ))

omit [BitWord.Selected model] in
private theorem preservesStore_then {post : RuntimeCtx model.kind}
    (first : Circuit model ctx ctx) (second : Circuit model ctx post)
    (predicate : Store ctx → Prop) (outputPredicate : Store post → Prop)
    (firstKeeps : PreservesStore first predicate)
    (secondKeeps : ∀ {Reference : Register} {H : Type} [Fintype H]
      (state : State ctx Reference (model.HiddenState × H)),
      (∀ entry, 0 < (state.block entry).mass → predicate entry.1) →
      ∀ result, 0 < ((second.execute Reference state).block result).mass →
        outputPredicate result.1)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate entry.1)
    (result : Store post × (model.HiddenState × (H × (first.seq second).Path)))
    (positive : 0 < (((first.seq second).execute Reference state).block result).mass) :
    outputPredicate result.1 := by
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have kept := secondKeeps (first.execute Reference state) (firstKeeps state holds) original present
  rw [← equality]
  exact kept

attribute [local irreducible] persistentCtx packBatchResultStep

private theorem packing_store_first
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (before : Store (persistentCtx ctx width scalarWidth))
    (holds : firstSelected width scalarWidth wanted before) :
    (packBatchResultStep ctx width scalarWidth before).1.read
      (batchResultRead ctx width scalarWidth) = .optionSome wanted := by
  rw [packBatchResultStep_output, holds.2]
  have accepted : before.read (.storage
      (persistentAccepted ctx width scalarWidth).toCStorageRef) = .bit true := by
    cases value : before.read (.storage
        (persistentAccepted ctx width scalarWidth).toCStorageRef) with
    | bit bitValue =>
        exact congrArg CShape.Value.bit
          (show bitValue = true by simpa only [value, CShape.Value.toBool] using holds.1)
  rw [accepted, CShape.packOption_true]

private theorem packing_supported_first
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      firstSelected width scalarWidth wanted entry.1)
    (result : Store (batchResultCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (packBatchResult ctx width scalarWidth).Path)))
    (positive : 0 < (((packBatchResult ctx width scalarWidth).execute Reference state).block
      result).mass) :
    result.1.read (batchResultRead ctx width scalarWidth) = .optionSome wanted := by
  let observe := fun entry : Store (batchResultCtx ctx width scalarWidth) × H =>
    entry.1.read (batchResultRead ctx width scalarWidth)
  have executed := packBatchResult_execute ctx width scalarWidth Reference state
  rw [executed] at positive
  have observedPositive : 0 < ((packBatchResultObserved ctx width scalarWidth observe
      Reference state).block (observe (result.1, result.2.2.1))).mass := by
    unfold packBatchResultObserved
    exact (mapped_positive _ _ _ _).mpr ⟨result, rfl, positive⟩
  rw [packBatchResult_observe] at observedPositive
  have expectedConstant : packBatchResultExpected ctx width scalarWidth observe Reference state =
      state.mapClassical (fun _ => CShape.Value.optionSome wanted) := by
    unfold packBatchResultExpected
    apply ExecutionState.mapClassical_eq_of_support
    intro entry present
    exact packing_store_first wanted entry.1 (holds entry present)
  rw [expectedConstant] at observedPositive
  by_contra different
  have opposite : CShape.Value.optionSome wanted ≠
      observe (result.1, result.2.2.1) := by
    intro equality
    exact different equality.symm
  rw [ExecutionState.mapClassical_block_mass] at observedPositive
  simp only [opposite, if_false, Finset.sum_const_zero, lt_self_iff_false] at observedPositive

/-- Every positive block keeps the same accepted first word through all actual sampling rounds. -/
theorem sampledAttempts_preserves_first
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true ∧
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState ×
        (H × (sampledAttempts sampleCode supported count curve modulus sample base target).Path)))
    (positive : 0 < (((sampledAttempts sampleCode supported count curve modulus sample base
      target).execute Reference state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        wanted := by
  exact preservesStore_forRange count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target)
    (firstSelected width scalarWidth wanted)
    (fun _ {Reference H} _ state =>
      sampledAttempt_preserves_first sampleCode supported curve modulus sample base target
        state wanted) state holds result positive

/-- Final real option packing returns the accepted first word after any further sampling count. -/
theorem sampledAttempts_pack_first_supported
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true ∧
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted)
    (result : Store (batchResultCtx ctx width scalarWidth) ×
      (model.HiddenState ×
        (H × ((sampledAttempts sampleCode supported count curve modulus sample base target).seq
          (packBatchResult ctx width scalarWidth)).Path)))
    (positive : 0 < ((((sampledAttempts sampleCode supported count curve modulus sample base
      target).seq (packBatchResult ctx width scalarWidth)).execute Reference state).block
        result).mass) :
    result.1.read (batchResultRead ctx width scalarWidth) = .optionSome wanted := by
  exact preservesStore_then
    (sampledAttempts sampleCode supported count curve modulus sample base target)
    (packBatchResult ctx width scalarWidth) (firstSelected width scalarWidth wanted)
    (fun store => store.read (batchResultRead ctx width scalarWidth) = .optionSome wanted)
    (fun {Reference H} _ state =>
      sampledAttempts_preserves_first sampleCode supported count curve modulus sample base target
        state wanted)
    (packing_supported_first wanted) state holds result positive

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
