/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Algorithms.OrderFinding.Probability
import all QuantumAlg.Algorithms.OrderFinding.Oracle
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Source amplitudes of the actual native order-finding word

The native Hadamards act on the original high-order phase bits while the
target register remains at zero. Subsequent oracle and inverse Fourier
equations use this same binary basis.
-/

namespace QuantumAlg.OrderFinding.Native

noncomputable section

open NormalizedVector
open scoped BigOperators

/-- The complete zero label is the tensor of the two original zero words. -/
private theorem zeroInput_eq_tensor (t width : Nat) :
    zeroInput t width =
      (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t))).tensor
        (NormalizedVector.ket (R := Qubits width) (0 : Fin (2 ^ width))) := by
  rw [NormalizedVector.tensor_ket]
  unfold zeroInput
  congr 1

/-- Native phase preparation produces the source's uniform phase word and zero target. -/
theorem initialLayer_apply_zero {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (initialLayer access).binaryMatrix.applyVec (zeroInput t width) =
      HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits width) (0 : Fin (2 ^ width)) :
          HilbertVector (Qubits width)) := by
  rw [initialLayer_binaryMatrix, zeroInput_eq_tensor]
  change ((WalshHadamard.hadamardLayerOperator t).tensor
    (1 : UnitaryOperator (Qubits width))).applyVec
      (HilbertVector.tensor
        (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t)) :
          HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits width) (0 : Fin (2 ^ width)) :
          HilbertVector (Qubits width))) = _
  rw [UnitaryOperator.tensor_applyVec_tensor, UnitaryOperator.one_applyVec]
  congr 1
  exact congrArg (fun state : NormalizedVector (Qubits t) =>
    (state : HilbertVector (Qubits t)))
    WalshHadamard.hadamardLayerOperator_apply_zero

/-- Periodic target fibers after the actual native XOR query. -/
def postOracleVec {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    HilbertVector (Qubits (t + width)) :=
  WithLp.toLp 2 fun basis =>
    let pair := prodEquiv.symm basis
    if pair.2 = modExpOracleTarget access pair.1 (0 : Fin (2 ^ width)) then
      WalshHadamard.invSqrtCard t
    else
      0

private theorem target_eq_zero_iff {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (phase : Fin (2 ^ t)) (target : Fin (2 ^ width)) :
    modExpOracleTarget access phase target = 0 ↔
      target = modExpOracleTarget access phase (0 : Fin (2 ^ width)) := by
  constructor
  · intro h
    have htwice := congrArg (modExpOracleTarget access phase) h
    simpa [modExpOracleTarget, Nat.xor_assoc] using htwice
  · intro h
    subst target
    apply Fin.ext
    simp [modExpOracleTarget]

/-- One declared native XOR query maps the prepared zero target to exact orbit fibers. -/
theorem oracleLayer_apply_initial {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (oracleLayer access).binaryMatrix.applyVec
        ((initialLayer access).binaryMatrix.applyVec (zeroInput t width)) =
      postOracleVec access := by
  rw [initialLayer_apply_zero, oracleLayer_binaryMatrix]
  apply WithLp.ofLp_injective
  funext basis
  change (modExpOracle access).applyVec
      (HilbertVector.tensor
        (WalshHadamard.uniformState t : HilbertVector (Qubits t))
        (NormalizedVector.ket (R := Qubits width) (0 : Fin (2 ^ width)) :
          HilbertVector (Qubits width))) basis =
    (if (prodEquiv.symm basis).2 =
        modExpOracleTarget access (prodEquiv.symm basis).1 0 then
      WalshHadamard.invSqrtCard t
    else
      0)
  rw [modExpOracle, UnitaryOperator.ofPerm_applyVec]
  change HilbertVector.tensor
      (WalshHadamard.uniformState t : HilbertVector (Qubits t))
      (NormalizedVector.ket (R := Qubits width) (0 : Fin (2 ^ width)) :
        HilbertVector (Qubits width))
      (prodEquiv ((prodEquiv.symm basis).1,
        modExpOracleTarget access (prodEquiv.symm basis).1
          (prodEquiv.symm basis).2)) = _
  rw [HilbertVector.tensor_apply_prod, WalshHadamard.uniformState_apply,
    NormalizedVector.ket_apply]
  rw [if_congr (target_eq_zero_iff access
    (prodEquiv.symm basis).1 (prodEquiv.symm basis).2) rfl rfl]
  by_cases htarget :
      (prodEquiv.symm basis).2 =
        modExpOracleTarget access (prodEquiv.symm basis).1 0
  · rw [if_pos htarget, if_pos htarget, mul_one]
  · rw [if_neg htarget, if_neg htarget, mul_zero]

/-- The source amplitude is the inverse Fourier sum over actual XOR-oracle fibers. -/
def sourceAmplitude {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (phase : Fin (2 ^ t)) (target : Fin (2 ^ width)) : ℂ :=
  ∑ exponent : Fin (2 ^ t),
    star (invSqrtN t * ω t ^ (exponent.val * phase.val)) *
      if target = modExpOracleTarget access exponent (0 : Fin (2 ^ width)) then
        WalshHadamard.invSqrtCard t
      else
        0

/-- The accepted native word has exactly the source geometric-sum amplitude. -/
theorem evolvedState_amplitude {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (phase : Fin (2 ^ t)) (target : Fin (2 ^ width)) :
    (evolvedState access).normalized (prodEquiv (phase, target)) =
      sourceAmplitude access phase target := by
  change ((circuit access).binaryMatrix.applyVec (zeroInput t width))
    (prodEquiv (phase, target)) = _
  rw [circuit_binaryMatrix, UnitaryOperator.mul_applyVec,
    UnitaryOperator.mul_applyVec,
    ← initialLayer_binaryMatrix access,
    ← oracleLayer_binaryMatrix access,
    ← readoutLayer_binaryMatrix access,
    oracleLayer_apply_initial, readoutLayer_binaryMatrix]
  change HilbertOperator.applyVec
      (((star (QFTOperator t)).tensor (1 : UnitaryOperator (Qubits width))) :
        HilbertOperator (Qubits (t + width)))
      (postOracleVec access) (prodEquiv (phase, target)) = _
  rw [HilbertOperator.applyVec_apply,
    ← Equiv.sum_comp (prodEquiv (m := t) (n := width)),
    Fintype.sum_prod_type]
  simp only [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, postOracleVec]
  rw [sourceAmplitude]
  apply Finset.sum_congr rfl
  intro exponent _
  rw [Finset.sum_eq_single target]
  · by_cases htarget :
        target = modExpOracleTarget access exponent (0 : Fin (2 ^ width))
    · simp [htarget]
    · simp [htarget]
  · intro other _ hother
    simp [Ne.symm hother]
  · simp

end

end QuantumAlg.OrderFinding.Native
