/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Retained
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public.Resources

/-!
# Actual retained XGCD native and complete space bounds

The retained result contributes its original unsigned gcd and both public
signed coefficient widths. Every original caller entry remains resident.
The arithmetic and packing scratch use their actual disjoint lifetimes, and
the actual retained allocation adds no arithmetic event or serial duration.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The retained public result remains live beside every actual public-body scratch cell. -/
def retainedAdditionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (XGCDOutputShape width) + publicScratchSpace kind width

/-- Retention introduces no native operations beyond the actual public body. -/
theorem xgcdNativeRetained_pool_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).resourcePool path ≤ publicEnvelope kind width := by
  exact xgcdNativePublicIntoResult_pool_le
    (input.underRetained key (XGCDOutputShape width) fresh)
    (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh) path.2

/-- Every original serial dependency retains its arbitrary native duration charge. -/
theorem xgcdNativeRetained_depth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (duration : Resource.Event kind → Nat)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).depth duration path ≤
      rawDepthLimit width duration + ((packingEvents kind width).map duration).sum := by
  change 0 + (publicIntoResult
    (input.underRetained key (XGCDOutputShape width) fresh)
    (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh)).depth duration path.2 ≤ _
  simpa only [zero_add] using xgcdNativePublicIntoResult_depth_le
    (input.underRetained key (XGCDOutputShape width) fresh)
    (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh) duration path.2

/-- The unchanged original width-derived native instruction ceiling includes the full packing. -/
theorem xgcdNativeRetained_unitDepth_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).depth (fun _ => 1) path ≤ 28 * width + 28 := by
  change 0 + (publicIntoResult
    (input.underRetained key (XGCDOutputShape width) fresh)
    (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh)).depth (fun _ => 1) path.2 ≤ _
  simpa only [zero_add] using xgcdNativePublicIntoResult_unitDepth_le
    (input.underRetained key (XGCDOutputShape width) fresh)
    (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh) path.2

/-- The resident peak includes the retained result, live scratch, and every caller entry. -/
theorem xgcdNativeRetained_resident_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).peakResidentSpace path ≤
      retainedAdditionalSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (.retain ctx key (XGCDOutputShape width) fresh)
    (publicIntoResult (input.underRetained key (XGCDOutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh)) path).le.trans ?_
  apply SpacePool.max_le
  · change SpacePool.max ctx.residentSpace
      (SpacePool.max (SpacePool.ofShape (XGCDOutputShape width) + ctx.residentSpace) 0) ≤ _
    rw [SpacePool.max_zero]
    apply SpacePool.max_le
    · exact le_add_of_nonneg_left zero_le
    · exact add_le_add (show SpacePool.ofShape (XGCDOutputShape width) ≤
        retainedAdditionalSpace kind width from le_add_of_nonneg_right zero_le) le_rfl
  · simpa only [retainedAdditionalSpace, RuntimeCtx.residentSpace_addRetained,
      add_assoc, add_comm, add_left_comm] using xgcdNativePublicIntoResult_resident_le
      (input.underRetained key (XGCDOutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh) path.2

/-- Retained output storage and all real scratch also contribute to the complete auxiliary peak. -/
theorem xgcdNativeRetained_auxiliary_le
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).peakAuxiliarySpace path ≤
      retainedAdditionalSpace kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (.retain ctx key (XGCDOutputShape width) fresh)
    (publicIntoResult (input.underRetained key (XGCDOutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh)) path).le.trans ?_
  apply SpacePool.max_le
  · change SpacePool.max ctx.auxiliarySpace
      (SpacePool.max (SpacePool.ofShape (XGCDOutputShape width) + ctx.auxiliarySpace) 0) ≤ _
    rw [SpacePool.max_zero]
    apply SpacePool.max_le
    · exact le_add_of_nonneg_left zero_le
    · exact add_le_add (show SpacePool.ofShape (XGCDOutputShape width) ≤
        retainedAdditionalSpace kind width from le_add_of_nonneg_right zero_le) le_rfl
  · simpa only [retainedAdditionalSpace, RuntimeCtx.auxiliarySpace_addRetained,
      add_assoc, add_comm, add_left_comm] using xgcdNativePublicIntoResult_auxiliary_le
      (input.underRetained key (XGCDOutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh) path.2

/-- The complete independent allowance preserves the full raw and public coefficient widths. -/
theorem xgcdNativeRetainedAdditional_classicalBits (kind : ProblemKind) (width : Nat) :
    retainedAdditionalSpace kind width .classicalBits =
      7 * width + 9 * PureXGCD.executionCoefficientWidth width +
        2 * coefficientWidth width + 1 := by
  change (SpacePool.ofShape (kind := kind) (XGCDOutputShape width)) .classicalBits +
    publicScratchSpace kind width .classicalBits = _
  rw [xgcdNativePublicScratch_classicalBits]
  have widthLe : coefficientWidth width ≤ PureXGCD.executionCoefficientWidth width :=
    ClassicalAlgorithms.NumberTheory.XGCD.coefficientWidth_le_executionCoefficientWidth width
  have rawDominates : 3 * coefficientWidth width ≤
      5 * width + 7 * PureXGCD.executionCoefficientWidth width + 1 := by omega
  rw [Nat.max_eq_left rawDominates]
  simp [SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
