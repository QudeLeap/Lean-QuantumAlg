/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing

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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

private theorem preservesStore_forRange (count : Nat) (body : Fin count → Circuit ctx ctx)
    (predicate : Store ctx → Prop) (keeps : ∀ index, PreservesStore (body index) predicate) :
    PreservesStore (Circuit.forRange count body) predicate := by
  induction count with
  | zero =>
      unfold PreservesStore
      intro Reference H _ state holds result positive
      change 0 < (((Circuit.id ctx).execute Reference state).block result).mass at positive
      rw [Circuit.execute_id_mapClassical] at positive
      obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
      rw [← equality]
      exact holds original present
  | succ count ih =>
      exact @preservesStore_seq kind ctx (body 0)
        (Circuit.forRange count (fun index => body index.succ)) predicate
        (@keeps 0) (ih (fun index => body index.succ) (fun index => @keeps index.succ))

private theorem preservesStore_then {post : RuntimeCtx kind}
    (first : Circuit ctx ctx) (second : Circuit ctx post)
    (predicate : Store ctx → Prop) (outputPredicate : Store post → Prop)
    (firstKeeps : PreservesStore first predicate)
    (secondKeeps : ∀ {Reference : Register} {H : Type} [Fintype H]
      (state : State ctx Reference H),
      (∀ entry, 0 < (state.block entry).mass → predicate entry.1) →
      ∀ result, 0 < ((second.execute Reference state).block result).mass →
        outputPredicate result.1)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate entry.1)
    (result : Store post × (H × (first.seq second).Path))
    (positive : 0 < (((first.seq second).execute Reference state).block result).mass) :
    outputPredicate result.1 := by
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have kept := secondKeeps (first.execute Reference state) (firstKeeps state holds) original present
  rw [← equality]
  exact kept

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

private theorem retainedStep_supported (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) {input output : CShape}
    (op : ClassicalOp input output
      (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh))
    (predicate : Store ctx → Prop)
    (outputPredicate : Store (ctx.addRetained key shape fresh) → Prop)
    (updates : ∀ before, predicate before →
      outputPredicate ((before.pushRetained key shape fresh).applyOp op))
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate entry.1)
    (result : Store (ctx.addRetained key shape fresh) ×
      (H × (Circuit.retainedStep ctx key shape fresh op).Path))
    (positive : 0 < (((Circuit.retainedStep ctx key shape fresh op).execute Reference state).block
      result).mass) : outputPredicate result.1 := by
  rw [Circuit.execute_retainedStep] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  rw [← equality]
  exact updates original.1 (holds original present)

private theorem packing_supported_first
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      firstSelected width scalarWidth wanted entry.1)
    (result : Store (batchResultCtx ctx width scalarWidth) ×
      (H × (packBatchResult ctx width scalarWidth).Path))
    (positive : 0 < (((packBatchResult ctx width scalarWidth).execute Reference state).block
      result).mass) :
    result.1.read (batchResultRead ctx width scalarWidth) = .optionSome wanted := by
  exact retainedStep_supported (persistentCtx ctx width scalarWidth).canonicalFreshKey
    (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (batchResultOp ctx width scalarWidth) (firstSelected width scalarWidth wanted)
    (fun store => store.read (batchResultRead ctx width scalarWidth) = .optionSome wanted)
    (packing_store_first wanted) state holds result positive

/-- Every positive block keeps the same accepted first word through all actual sampling rounds. -/
theorem sampledAttempts_preserves_first
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    {H : Type} [Fintype H] (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true ∧
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (sampledAttempts sampleCode supported count curve modulus sample base target).Path))
    (positive : 0 < (((sampledAttempts sampleCode supported count curve modulus sample base
      target).execute Reference state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        wanted := by
  exact @preservesStore_forRange kind (persistentCtx ctx width scalarWidth) count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target)
    (firstSelected width scalarWidth wanted)
    (fun _ {Reference H} _ state =>
      @sampledAttempt_preserves_first kind ctx width scalarWidth sampleCode supported
        curve modulus sample base target Reference H _ state wanted) Reference H _ state holds
          result positive

/-- Final real option packing returns the accepted first word after any further sampling count. -/
theorem sampledAttempts_pack_first_supported
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    {H : Type} [Fintype H] (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true ∧
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted)
    (result : Store (batchResultCtx ctx width scalarWidth) ×
      (H × ((sampledAttempts sampleCode supported count curve modulus sample base target).seq
        (packBatchResult ctx width scalarWidth)).Path))
    (positive : 0 < ((((sampledAttempts sampleCode supported count curve modulus sample base
      target).seq (packBatchResult ctx width scalarWidth)).execute Reference state).block
        result).mass) :
    result.1.read (batchResultRead ctx width scalarWidth) = .optionSome wanted := by
  exact @preservesStore_then kind (persistentCtx ctx width scalarWidth)
    (batchResultCtx ctx width scalarWidth)
    (sampledAttempts sampleCode supported count curve modulus sample base target)
    (packBatchResult ctx width scalarWidth) (firstSelected width scalarWidth wanted)
    (fun store => store.read (batchResultRead ctx width scalarWidth) = .optionSome wanted)
    (fun {Reference H} _ state =>
      @sampledAttempts_preserves_first kind ctx width scalarWidth sampleCode supported count
        curve modulus sample base target Reference H _ state wanted)
    (@packing_supported_first kind ctx width scalarWidth wanted) Reference H _ state holds result
      positive

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
