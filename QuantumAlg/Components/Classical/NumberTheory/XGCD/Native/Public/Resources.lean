/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Packing.Resources
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Resources
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Space

/-!
# Real public XGCD allocation and native resource bounds

The three raw outputs remain live throughout arithmetic and public packing.
The two phases reuse their lexical scratch lifetime, so the scratch allowance
uses their maximum. The caller's complete resident and auxiliary interfaces
are retained, including the public result supplied by the caller.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original raw engine allowance followed by the actual five packing operations. -/
def publicEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : ResourcePool
  model :=
  rawEnvelope model width + ResourcePool.ofList (packingEvents model width)

/-- Only the maximum of raw-engine and packing scratch is simultaneously resident. -/
def publicPhaseSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (rawScratchSpace kind width)
    (((packingShapes width).map SpacePool.ofShape).sum)

/-- All three raw outputs remain live beside the maximum scratch of the two actual phases. -/
def publicScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  ((publicRawShapes width).map SpacePool.ofShape).sum + publicPhaseSpace kind width

private lemma publicBody_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicBody (model := model) input outputs result).Path) :
    (publicBody (model := model) input outputs result).resourcePool path ≤ publicEnvelope model
      width := by
  change ResourcePool.ofList ((rawEngine (model := model) input outputs).eventTrace path.1 ++
    (packRawOutputs (model := model) outputs result).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, xgcdNativePackRawOutputs_eventTrace]
  exact add_le_add (xgcdNativeRawEngine_pool_le input outputs path.1) le_rfl

/-- Every actual public path obeys the original raw and nominal-packing native allowance. -/
lemma xgcdNativePublicIntoResult_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicIntoResult (model := model) input result).Path) :
    (publicIntoResult (model := model) input result).resourcePool path ≤ publicEnvelope model width
      := by
  exact withCellsFrom_pool_le (Transport.id ctx) (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result)) (publicEnvelope model width)
    (fun cells _ transport _ selected => publicBody_pool_le _ _ _ selected) path

private lemma publicBody_depth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (result : CWriteRef ctx (XGCDOutputShape width))
    (duration : Resource.Event model → Nat) (path : (publicBody (model := model) input outputs
      result).Path) :
    (publicBody (model := model) input outputs result).depth duration path ≤
      rawDepthLimit width duration + ((packingEvents model width).map duration).sum := by
  change (rawEngine (model := model) input outputs).depth duration path.1 +
    (packRawOutputs (model := model) outputs result).depth duration path.2 ≤ _
  rw [xgcdNativePackRawOutputs_depth]
  exact Nat.add_le_add_right (xgcdNativeRawEngine_depth_le input outputs duration path.1) _

/-- All original serial dependencies remain charged for arbitrary native durations. -/
lemma xgcdNativePublicIntoResult_depth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (duration : Resource.Event model → Nat)
    (path : (publicIntoResult (model := model) input result).Path) :
    (publicIntoResult (model := model) input result).depth duration path ≤
      rawDepthLimit width duration + ((packingEvents model width).map duration).sum := by
  exact withCellsFrom_depth_le (Transport.id ctx) (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result)) duration _
    (fun cells _ transport _ selected => publicBody_depth_le _ _ _ duration selected) path

/-- The actual public path uses at most the original raw bound plus five packing instructions. -/
lemma xgcdNativePublicIntoResult_unitDepth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicIntoResult (model := model) input result).Path) :
    (publicIntoResult (model := model) input result).depth (fun _ => 1) path ≤ 28 * width + 28 := by
  have bound := xgcdNativePublicIntoResult_depth_le input result (fun _ => 1) path
  rw [xgcdNativeRawDepthLimit_unit] at bound
  change _ ≤ 28 * width + 23 + 5 at bound
  omega

private lemma publicBody_resident_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicBody (model := model) input outputs result).Path) :
    (publicBody (model := model) input outputs result).peakResidentSpace path ≤
      publicPhaseSpace model.kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (rawEngine (model := model) input outputs)
    (packRawOutputs (model := model) outputs result) path).le.trans ?_
  apply SpacePool.max_le
  · exact (xgcdNativeRawEngine_resident_le input outputs path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (xgcdNativePackRawOutputs_resident outputs result path.2).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The real raw-result allocation retains every caller cell through both execution phases. -/
lemma xgcdNativePublicIntoResult_resident_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicIntoResult (model := model) input result).Path) :
    (publicIntoResult (model := model) input result).peakResidentSpace path ≤
      publicScratchSpace model.kind width + ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result)) (publicPhaseSpace model.kind width)
    (fun cells _ transport _ selected => publicBody_resident_le _ _ _ selected) path

private lemma publicBody_auxiliary_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (outputs : RawOutputs ctx width) (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicBody (model := model) input outputs result).Path) :
    (publicBody (model := model) input outputs result).peakAuxiliarySpace path ≤
      publicPhaseSpace model.kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (rawEngine (model := model) input outputs)
    (packRawOutputs (model := model) outputs result) path).le.trans ?_
  apply SpacePool.max_le
  · exact (xgcdNativeRawEngine_auxiliary_le input outputs path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (xgcdNativePackRawOutputs_auxiliary outputs result path.2).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- Every temporary raw-result, arithmetic and packing cell contributes to the auxiliary peak. -/
lemma xgcdNativePublicIntoResult_auxiliary_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (publicIntoResult (model := model) input result).Path) :
    (publicIntoResult (model := model) input result).peakAuxiliarySpace path ≤
      publicScratchSpace model.kind width + ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result)) (publicPhaseSpace model.kind width)
    (fun cells _ transport _ selected => publicBody_auxiliary_le _ _ _ selected) path

/-- The independent scratch formula counts the original widths and the actual lifetime maximum. -/
lemma xgcdNativePublicScratch_classicalBits (kind : ProblemKind) (width : Nat) :
    publicScratchSpace kind width .classicalBits =
      width + 2 * PureXGCD.executionCoefficientWidth width +
        max (5 * width + 7 * PureXGCD.executionCoefficientWidth width + 1)
          (3 * coefficientWidth width) := by
  change (((publicRawShapes width).map (SpacePool.ofShape (kind := kind))).sum) .classicalBits +
    max (rawScratchSpace kind width .classicalBits)
      ((((packingShapes width).map (SpacePool.ofShape (kind := kind))).sum) .classicalBits) = _
  rw [xgcdNativeRawScratch_classicalBits, xgcdNativePackingShapes_classicalBits]
  simp [publicRawShapes, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
