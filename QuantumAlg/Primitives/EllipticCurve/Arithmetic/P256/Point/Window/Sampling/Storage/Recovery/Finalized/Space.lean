/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Resources.Bounds

/-!
# Space of the actual terminally cleaned three-attempt circuit

The final physical reset is an allocation-free child in the existing feedback
frame. Its complete resident and auxiliary peaks are therefore the already
live inner context. Retained checker destinations, attempt scratch, feedback
cells and the final packed option have the same peaks as the original run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution ClassicalWorkspace ClassicalRoutines

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx)

private lemma finalized_frame_extra_le :
    frameSpace .quantum 256 256 + attemptAdditionalSpace ≤ runAdditionalSpace :=
  SpacePool.le_max_left _ _

private lemma finalized_output_extra_le :
    SpacePool.ofShape (.option (.unsignedWord 260)) ≤ runAdditionalSpace :=
  SpacePool.le_max_right _ _

attribute [local irreducible] scopedAttemptsFinalized withFrame
  attemptAdditionalSpace runAdditionalSpace
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace

private lemma loop_cleanup_resident_le {model : ExecutionModel}
    {inner : RuntimeCtx model.kind} {allocation : Bool}
    (body : Circuit model inner inner allocation) (cleanup : Circuit model inner inner false)
    (budget : SpacePool model.kind) (count : Nat) (entry : inner.residentSpace ≤ budget)
    (bounded : ∀ path, body.peakResidentSpace path ≤ budget)
    (path : ((Circuit.forRange count fun _ => body).seq
      (.embed (ContextEmbedding.identity inner) cleanup)).Path) :
    ((Circuit.forRange count fun _ => body).seq
      (.embed (ContextEmbedding.identity inner) cleanup)).peakResidentSpace path ≤ budget := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact Circuit.forRange_resident_le count (fun _ => body) budget entry
      (fun _ => bounded) path.1
  · exact (Circuit.peakResidentSpace_embed (allowAllocation := allocation)
      (ContextEmbedding.identity inner) cleanup path.2).le.trans entry

private lemma loop_cleanup_auxiliary_le {model : ExecutionModel}
    {inner : RuntimeCtx model.kind} {allocation : Bool}
    (body : Circuit model inner inner allocation) (cleanup : Circuit model inner inner false)
    (budget : SpacePool model.kind) (count : Nat) (entry : inner.auxiliarySpace ≤ budget)
    (bounded : ∀ path, body.peakAuxiliarySpace path ≤ budget)
    (path : ((Circuit.forRange count fun _ => body).seq
      (.embed (ContextEmbedding.identity inner) cleanup)).Path) :
    ((Circuit.forRange count fun _ => body).seq
      (.embed (ContextEmbedding.identity inner) cleanup)).peakAuxiliarySpace path ≤ budget := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact Circuit.forRange_auxiliary_le count (fun _ => body) budget entry
      (fun _ => bounded) path.1
  · exact (Circuit.peakAuxiliarySpace_embed (allowAllocation := allocation)
      (ContextEmbedding.identity inner) cleanup path.2).le.trans entry

private lemma finalizedInnerBody_resident_le
    {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (selected : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    (inputs.finalizedInnerBody (services := services) sampler checkers count).peakResidentSpace
      selected ≤ attemptAdditionalSpace + inner.residentSpace := by
  exact loop_cleanup_resident_le
    (inputs.attempt (services := services) sampler checkers)
    ((finalizedCleanup sampler).circuit (services := services))
    (attemptAdditionalSpace + inner.residentSpace) count (le_add_of_nonneg_left zero_le)
    (inputs.attempt_resident_le (services := services) sampler checkers) selected

private lemma finalizedInnerBody_auxiliary_le
    {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (selected : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    (inputs.finalizedInnerBody (services := services) sampler checkers count).peakAuxiliarySpace
      selected ≤ attemptAdditionalSpace + inner.auxiliarySpace := by
  exact loop_cleanup_auxiliary_le
    (inputs.attempt (services := services) sampler checkers)
    ((finalizedCleanup sampler).circuit (services := services))
    (attemptAdditionalSpace + inner.auxiliarySpace) count (le_add_of_nonneg_left zero_le)
    (inputs.attempt_auxiliary_le (services := services) sampler checkers) selected

/-- Terminal whole-bank cleanup reuses the live inner context after the
attempts, so the single feedback frame keeps its original resident bound. -/
lemma scopedAttemptsFinalized_resident_le (count : Nat)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    (original.scopedAttemptsFinalized (services := services) count).peakResidentSpace path ≤
      frameSpace .quantum 256 256 + attemptAdditionalSpace +
        (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
  unfold Circuit.peakResidentSpace
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_peak_le (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    256 256 _ RuntimeCtx.residentSpace
    RuntimeCtx.residentSpace_addWorkspace attemptAdditionalSpace ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  simpa only [Circuit.peakResidentSpace] using
    inputs.finalizedInnerBody_resident_le (services := services) sampler checkers count selected

/-- The terminally cleaned run retains the original complete resident-space
allowance, including the one-time seven-cell checker frame and packed output. -/
lemma runFinalized_resident_le
    (path : (original.runFinalized (services := services)).code.Path) :
    (original.runFinalized (services := services)).code.peakResidentSpace path ≤
      runAdditionalSpace +
        EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum 256 260 +
          ctx.residentSpace := by
  have repeated := (original.scopedAttemptsFinalized_resident_le
    (services := services) 3 path.1.2).trans (add_le_add finalized_frame_extra_le le_rfl)
  have actual : (original.runFinalized (services := services)).code.peakResidentSpace path ≤
      runAdditionalSpace +
        (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans
        (SpacePool.max_le ?_ repeated)
      exact (EllipticCurve.CandidateCheck.Native.retainPersistent_resident
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.1.1).le.trans (le_add_of_nonneg_left zero_le)
    · exact (EllipticCurve.CandidateCheck.Native.packBatchResult_resident
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.2).le.trans (add_le_add finalized_output_extra_le le_rfl)
  simpa only [EllipticCurve.CandidateCheck.Native.persistentCtx_residentSpace, add_assoc]
    using actual

/-- The same allocation-free terminal reset adds no auxiliary role inside
the reused feedback frame. -/
lemma scopedAttemptsFinalized_auxiliary_le (count : Nat)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    (original.scopedAttemptsFinalized (services := services) count).peakAuxiliarySpace path ≤
      frameSpace .quantum 256 256 + attemptAdditionalSpace +
        (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
  unfold Circuit.peakAuxiliarySpace
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_peak_le (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    256 256 _ RuntimeCtx.auxiliarySpace
    RuntimeCtx.auxiliarySpace_addWorkspace attemptAdditionalSpace ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  simpa only [Circuit.peakAuxiliarySpace] using
    inputs.finalizedInnerBody_auxiliary_le (services := services) sampler checkers count selected

/-- The complete terminally cleaned program keeps the old auxiliary-space
allowance through the final original result pack. -/
lemma runFinalized_auxiliary_le
    (path : (original.runFinalized (services := services)).code.Path) :
    (original.runFinalized (services := services)).code.peakAuxiliarySpace path ≤
      runAdditionalSpace +
        EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum 256 260 +
          ctx.auxiliarySpace := by
  have repeated := (original.scopedAttemptsFinalized_auxiliary_le
    (services := services) 3 path.1.2).trans (add_le_add finalized_frame_extra_le le_rfl)
  have actual : (original.runFinalized (services := services)).code.peakAuxiliarySpace path ≤
      runAdditionalSpace +
        (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans
        (SpacePool.max_le ?_ repeated)
      exact (EllipticCurve.CandidateCheck.Native.retainPersistent_auxiliary
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.1.1).le.trans (le_add_of_nonneg_left zero_le)
    · exact (EllipticCurve.CandidateCheck.Native.packBatchResult_auxiliary
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.2).le.trans (add_le_add finalized_output_extra_le le_rfl)
  simpa only [EllipticCurve.CandidateCheck.Native.persistentCtx_auxiliarySpace, add_assoc]
    using actual

end

end Storage.Inputs

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
