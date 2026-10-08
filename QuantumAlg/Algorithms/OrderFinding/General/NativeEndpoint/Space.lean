/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Space
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Complete live storage of connected native order finding

The independent budget includes all source qubits and result bits, the
retained option, and the finite recovery scratch peak. Resident and auxiliary
proofs account for the caller's borrowed base on separate input ledgers.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

/-- Extra finite-recovery scratch charged on top of the retained sample. -/
def recoveryBits (t width : Nat) : Nat :=
  ClassicalRoutines.OrderRecovery.Native.extraClassicalBits width t

/-- Independent source, final-result and finite-recovery live capacity. -/
def spaceBudget (t width : Nat) : SpacePool .quantum :=
  Sampling.Native.spaceBudget t width +
    SpacePool.ofShape (.bits (t + 2 + recoveryBits t width))

private theorem sample_resident_eq (t width : Nat) :
    (SourceNativeSampling.post t width).residentSpace =
      Sampling.Native.spaceBudget t width + (pre width).residentSpace := by
  exact Sampling.Native.Framed.post_residentSpace (pre width)
    (pre_quantumWires width) t width

private theorem sample_auxiliary_eq (t width : Nat) :
    (SourceNativeSampling.post t width).auxiliarySpace =
      Sampling.Native.spaceBudget t width + (pre width).auxiliarySpace := by
  exact Sampling.Native.Framed.post_auxiliarySpace (pre width)
    (pre_quantumWires width) t width

private theorem final_resident_eq (t width : Nat) :
    (post t width).residentSpace + SpacePool.ofShape (.bits (recoveryBits t width)) =
      spaceBudget t width + (pre width).residentSpace := by
  rw [post, RuntimeCtx.residentSpace_addRetained, sample_resident_eq]
  ext axis
  cases axis <;> simp [spaceBudget, outputShape, SpacePool.ofShape]
  omega

private theorem final_auxiliary_eq (t width : Nat) :
    (post t width).auxiliarySpace + SpacePool.ofShape (.bits (recoveryBits t width)) =
      spaceBudget t width + (pre width).auxiliarySpace := by
  rw [post, RuntimeCtx.auxiliarySpace_addRetained, sample_auxiliary_eq]
  ext axis
  cases axis <;> simp [spaceBudget, outputShape, SpacePool.ofShape]
  omega

private theorem sample_resident_le (t width : Nat) :
    Sampling.Native.spaceBudget t width + (pre width).residentSpace ≤
      spaceBudget t width + (pre width).residentSpace := by
  intro axis
  change Sampling.Native.spaceBudget t width axis + (pre width).residentSpace axis ≤
    (Sampling.Native.spaceBudget t width axis +
      SpacePool.ofShape (.bits (t + 2 + recoveryBits t width)) axis) +
      (pre width).residentSpace axis
  omega

private theorem sample_auxiliary_le (t width : Nat) :
    Sampling.Native.spaceBudget t width + (pre width).auxiliarySpace ≤
      spaceBudget t width + (pre width).auxiliarySpace := by
  intro axis
  change Sampling.Native.spaceBudget t width axis + (pre width).auxiliarySpace axis ≤
    (Sampling.Native.spaceBudget t width axis +
      SpacePool.ofShape (.bits (t + 2 + recoveryBits t width)) axis) +
      (pre width).auxiliarySpace axis
  omega

/-- Every connected execution path respects the independent resident limit. -/
theorem code_resident_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) (path : (code hinput access).Path) :
    (code hinput access).peakResidentSpace path ≤
      spaceBudget t width + (pre width).residentSpace := by
  change (Circuit.seq (SourceNativeSampling.code access)
    (Circuit.seq (Circuit.retain (model := Sampling.Native.Framed.model access)
      (SourceNativeSampling.post t width) (resultKey t width)
      (outputShape t) (resultFresh t width))
      (recoveryCode hinput access))).Path at path
  change (Circuit.seq (SourceNativeSampling.code access)
    (Circuit.seq (Circuit.retain (model := Sampling.Native.Framed.model access)
      (SourceNativeSampling.post t width) (resultKey t width)
      (outputShape t) (resultFresh t width))
      (recoveryCode hinput access))).peakResidentSpace path ≤ _
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · exact (SourceNativeSampling.residentSpace access path.1).trans
      (sample_resident_le t width)
  · rw [Circuit.peakResidentSpace_seq]
    apply SpacePool.max_le
    · rw [Circuit.peakResidentSpace_retain]
      exact (le_add_of_nonneg_right zero_le).trans_eq
        (final_resident_eq t width)
    · exact (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_resident_le
        (model := Sampling.Native.Framed.model access)
        (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
        (resultRef t width) path.2.2).trans_eq (final_resident_eq t width)

/-- Auxiliary storage keeps the original borrowed input outside new scratch. -/
theorem code_auxiliary_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) (path : (code hinput access).Path) :
    (code hinput access).peakAuxiliarySpace path ≤
      spaceBudget t width + (pre width).auxiliarySpace := by
  change (Circuit.seq (SourceNativeSampling.code access)
    (Circuit.seq (Circuit.retain (model := Sampling.Native.Framed.model access)
      (SourceNativeSampling.post t width) (resultKey t width)
      (outputShape t) (resultFresh t width))
      (recoveryCode hinput access))).Path at path
  change (Circuit.seq (SourceNativeSampling.code access)
    (Circuit.seq (Circuit.retain (model := Sampling.Native.Framed.model access)
      (SourceNativeSampling.post t width) (resultKey t width)
      (outputShape t) (resultFresh t width))
      (recoveryCode hinput access))).peakAuxiliarySpace path ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · exact (SourceNativeSampling.auxiliarySpace access path.1).trans
      (sample_auxiliary_le t width)
  · rw [Circuit.peakAuxiliarySpace_seq]
    apply SpacePool.max_le
    · rw [Circuit.peakAuxiliarySpace_retain]
      exact (le_add_of_nonneg_right zero_le).trans_eq
        (final_auxiliary_eq t width)
    · exact (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_auxiliary_le
        (model := Sampling.Native.Framed.model access)
        (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
        (resultRef t width) path.2.2).trans_eq (final_auxiliary_eq t width)

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
