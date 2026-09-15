/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Semantics
import all QuantumAlg.Core.Execution.MappedTail

/-!
# Complete actual persistent recovery execution

Actual seven-cell allocation supplies the initial store of the chronological
attempt loop. Actual final retention and option packing then read the loop's
returned latches. These complete execution equations retain every quantum
reference block, original history and real path of all three stages.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth count : Nat}

/-- The actual allocated initial store feeds the original ordered attempt updates. -/
def recoveryBatchStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx) :
    Store (persistentCtx ctx width scalarWidth) :=
  repeatedAttemptsStore curve modulus samples base target
    (persistentInitialStore width scalarWidth before)

/-- Actual optional-result retention and packing consume the real loop's returned store. -/
def recoveryTailStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx) :
    Store (batchResultCtx ctx width scalarWidth) :=
  (packBatchResultStep ctx width scalarWidth
    (recoveryBatchStore curve modulus samples base target before)).1

/-- Map the actual complete recovery batch record over all incoming reference blocks. -/
def recoveryBatchRecordState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (record : Store ctx → Store (persistentCtx ctx width scalarWidth) ×
      (recoveryBatch curve modulus samples base target).Path)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    State (persistentCtx ctx width scalarWidth) Reference
      (History × (recoveryBatch curve modulus samples base target).Path) :=
  state.mapClassical (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2)))

/-- Map the actual complete recovery tail record over all incoming reference blocks. -/
def recoveryTailRecordState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (record : Store ctx → Store (batchResultCtx ctx width scalarWidth) ×
      (recoveryTail curve modulus samples base target).Path)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    State (batchResultCtx ctx width scalarWidth) Reference
      (History × (recoveryTail curve modulus samples base target).Path) :=
  state.mapClassical (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2)))

private theorem deterministicTail_after {pre middle : RuntimeCtx kind}
    (first : Circuit pre middle) (second : Circuit middle middle)
    (record : Store middle → Store middle × second.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State middle Reference History), second.execute Reference state =
        state.mapClassical (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference History) :
    (first.seq second).execute Reference state =
      (first.execute Reference state).mapClassical (fun entry =>
        ((record entry.1).1, (entry.2.1, (entry.2.2, (record entry.1).2)))) := by
  rw [Circuit.execute_seq, equation]
  simp only [State.mapHistory]
  exact persistentTwoMaps_eq _ _ _ (first.execute Reference state) _ _

/-- The actual allocator and complete loop preserve the entire incoming reference and history. -/
theorem recoveryBatch_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    ∃ record : Store ctx → Store (persistentCtx ctx width scalarWidth) ×
        (recoveryBatch curve modulus samples base target).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (recoveryBatch curve modulus samples base target).execute Reference state =
          recoveryBatchRecordState curve modulus samples base target record Reference state) ∧
      ∀ before : Store ctx, (record before).1 =
        recoveryBatchStore curve modulus samples base target before := by
  obtain ⟨loopRecord, loopEquation, loopStore⟩ :=
    repeatedAttempts_actualRecord curve modulus samples base target
  let record : Store ctx → Store (persistentCtx ctx width scalarWidth) ×
      (recoveryBatch curve modulus samples base target).Path := fun before =>
    let allocated := persistentAllocationStep width scalarWidth before
    let looped := loopRecord allocated.1
    (looped.1, (allocated.2, looped.2))
  refine ⟨record, ?_, ?_⟩
  · intro Reference History historyFinite state
    have whole := deterministicTail_after (retainPersistent ctx width scalarWidth)
      (repeatedAttempts curve modulus samples base target) loopRecord loopEquation Reference state
    conv at whole =>
      rhs
      arg 1
      rw [retainPersistent_execute]
      unfold persistentAllocationState
    conv at whole =>
      rhs
      erw [persistentTwoMaps_eq _ _ (Classical.decEq _) state _ _]
    refine whole.trans ?_
    unfold recoveryBatchRecordState
    exact (Circuit.mapClassical_canonicalDecision _ state _).symm
  · intro before
    exact loopStore (persistentInitialStore width scalarWidth before)

/-- Final actual packing retains the complete allocated-loop record and original input history. -/
theorem recoveryTail_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    ∃ record : Store ctx → Store (batchResultCtx ctx width scalarWidth) ×
        (recoveryTail curve modulus samples base target).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (recoveryTail curve modulus samples base target).execute Reference state =
          recoveryTailRecordState curve modulus samples base target record Reference state) ∧
      ∀ before : Store ctx, (record before).1 =
        recoveryTailStore curve modulus samples base target before := by
  obtain ⟨batchRecord, batchEquation, batchStore⟩ :=
    recoveryBatch_actualRecord curve modulus samples base target
  let record : Store ctx → Store (batchResultCtx ctx width scalarWidth) ×
      (recoveryTail curve modulus samples base target).Path := fun before =>
    let looped := batchRecord before
    let packed := packBatchResultStep ctx width scalarWidth looped.1
    (packed.1, (looped.2, packed.2))
  refine ⟨record, ?_, ?_⟩
  · intro Reference History historyFinite state
    let finalFinite : Fintype (Store ((persistentCtx ctx width scalarWidth).addRetained
        (persistentCtx ctx width scalarWidth).canonicalFreshKey
        (.option (.unsignedWord scalarWidth))
        (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh) × History ×
        (recoveryBatch curve modulus samples base target).Path ×
        (packBatchResult ctx width scalarWidth).Path) := inferInstance
    have whole := Circuit.execute_seq_retained_mapClassical_tail
      (persistentCtx ctx width scalarWidth).canonicalFreshKey
      (.option (.unsignedWord scalarWidth))
      (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
      (recoveryBatch curve modulus samples base target) (packBatchResult ctx width scalarWidth)
      (packBatchResultStep ctx width scalarWidth)
      (fun Reference _ _ state => packBatchResult_execute ctx width scalarWidth Reference state)
      Reference state
    conv at whole =>
      rhs
      arg 1
      rw [batchEquation]
      unfold recoveryBatchRecordState
    conv at whole =>
      rhs
      erw [@persistentTwoMaps_eq _ _ _ _ _ finalFinite _ _ _ (Classical.decEq _)
        state _ _]
    refine whole.trans ?_
    unfold recoveryTailRecordState
    exact (@Circuit.mapClassical_canonicalDecision _ _ _ finalFinite _ _ state _).symm
  · intro before
    exact congrArg (fun current => (packBatchResultStep ctx width scalarWidth current).1)
      (batchStore before)

/-- The complete actual tail returns the option encoded by its final persistent latches. -/
theorem recoveryTailStore_output (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx) :
    (recoveryTailStore curve modulus samples base target before).read
      (batchResultRead ctx width scalarWidth) =
        CShape.packOption (.product
          ((recoveryBatchStore curve modulus samples base target before).read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
          ((recoveryBatchStore curve modulus samples base target before).read
            (.storage (persistentSelected ctx width scalarWidth).toCStorageRef))) :=
  packBatchResultStep_output ctx width scalarWidth
    (recoveryBatchStore curve modulus samples base target before)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
