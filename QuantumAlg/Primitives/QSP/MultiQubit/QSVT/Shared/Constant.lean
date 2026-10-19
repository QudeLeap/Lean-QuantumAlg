/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Rotation.Operator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Query-free initial phases for real constant branches

The rotation angle depends only on the specified polynomial constant. Its
plus-state block is that constant times identity on the complete source
suffix. No source-unitary entry is inspected and no source query is executed.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

private lemma rotation_plus_block (width : Nat) (angle : ℝ) :
    phasePlusBlock ((rotZOp angle).tensor (1 : UnitaryOperator (Qubits width))) =
      (Real.cos angle : ℂ) • (1 : HilbertOperator (Qubits width)) := by
  rw [phasePlusBlock_eq_sum_ancillaBlock]
  have identityMatrix : ((1 : UnitaryOperator (Qubits width)) :
      HilbertOperator (Qubits width)) = 1 := rfl
  simp only [UnitaryOperator.coe_tensor, identityMatrix, Nat.reducePow, Fin.sum_univ_two,
    ancillaBlock_tensor_left, NormalizedVector.ketPlus_apply, smul_smul]
  have hstar : (starRingEnd ℂ) NormalizedVector.invSqrt2 = NormalizedVector.invSqrt2 :=
    NormalizedVector.star_invSqrt2
  rw [hstar]
  have mean : (1 / 2 : ℂ) *
      (Complex.exp ((angle : ℂ) * Complex.I) + Complex.exp (-((angle : ℂ) * Complex.I))) =
      (Real.cos angle : ℂ) := by
    rw [show -((angle : ℂ) * Complex.I) = (-angle : ℂ) * Complex.I by ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
    ring
  have r00 : rotZOp angle (0 : Fin 2) 0 = Complex.exp ((angle : ℂ) * Complex.I) := rfl
  have r01 : rotZOp angle (0 : Fin 2) 1 = 0 := rfl
  have r10 : rotZOp angle (1 : Fin 2) 0 = 0 := rfl
  have r11 : rotZOp angle (1 : Fin 2) 1 = Complex.exp (-((angle : ℂ) * Complex.I)) := rfl
  simp only [r00, r01, r10, r11, mul_zero, zero_smul, add_zero, zero_add]
  rw [← add_smul, ← mul_add, ← mul_add, ← mul_assoc, NormalizedVector.invSqrt2_mul_self]
  simpa only [one_div] using congrArg (fun scalar : ℂ =>
    scalar • (1 : HilbertOperator (Qubits width))) mean

/-- A real constant is represented by an actual phase rotation, valid even for an empty suffix. -/
def constantInitial (oracles : OracleModel) (width : Nat) (constant : ℝ) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  Gate.singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout oracles
    (rotZOp (Real.arccos constant)) (0 : Fin (1 + width)) rfl

/-- The complete plus-state block equals the known real constant on the unchanged source. -/
lemma constantInitial_correct (oracles : OracleModel) (width : Nat) (constant : ℝ)
    (lower : -1 ≤ constant) (upper : constant ≤ 1) (environment : oracles.Interpretation) :
    phasePlusBlock ((constantInitial oracles width constant).binaryMatrix environment) =
      (constant : ℂ) • (1 : HilbertOperator (Qubits width)) := by
  rw [constantInitial, Gate.singleQubitAt_first_binaryMatrix, rotation_plus_block,
    Real.cos_arccos lower upper]

/-- Constant branch initialization contributes one native rotation and no query. -/
lemma constantInitial_events (oracles : OracleModel) (width : Nat) (constant : ℝ) :
    (constantInitial oracles width constant).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := rfl

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
