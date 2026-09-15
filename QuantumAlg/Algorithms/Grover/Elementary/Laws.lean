/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace

import all QuantumAlg.Algorithms.Grover.Elementary.Construction
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Components.Oracle.ZeroReflection.Small.Program
import all QuantumAlg.Components.Oracle.ZeroReflection.OneDirty.Program
import all QuantumAlg.Components.Oracle.ZeroReflection
import all QuantumAlg.Core.Base.UnitaryCircuit.IdleSuffix
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact operator and prepared state of the elementary Grover execution

The actual elementary sequence equals the original Grover operator tensor
identity on the selected work suffix. This is a full-space equality before
preparation or measurement, so it introduces no work-state premise. The
internally prepared all-zero work value is retained in the final vector.
-/

namespace QuantumAlg.GroverSearch.Elementary

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

theorem hadamards_matrix (n k : Nat) :
    (hadamards n k).matrix = UnitaryOperator.tensor (initialPreparationCircuit n).matrix
      (1 : UnitaryOperator (Qubits (helperWidth n k))) :=
  UnitaryCircuit.idleSuffix_matrix _ _ _

theorem oracle_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (oracle marked k).matrix = UnitaryOperator.tensor (phaseOracleCircuit marked).matrix
      (1 : UnitaryOperator (Qubits (helperWidth n k))) :=
  UnitaryCircuit.idleSuffix_matrix _ _ _

private theorem hadamards_dagger_matrix (n k : Nat) :
    (hadamards n k).dagger.matrix =
      UnitaryOperator.tensor (initialPreparationCircuit n).matrix.dagger
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  apply Subtype.ext
  rw [UnitaryCircuit.dagger_matrix, hadamards_matrix]
  simp only [UnitaryOperator.coe_tensor, UnitaryOperator.coe_dagger]
  change (HilbertOperator.tensor
    ((initialPreparationCircuit n).matrix : HilbertOperator (Qubits n))
    (1 : HilbertOperator (Qubits (helperWidth n k)))).conjTranspose =
      HilbertOperator.tensor
        ((initialPreparationCircuit n).matrix : HilbertOperator (Qubits n)).conjTranspose 1
  rw [HilbertOperator.conjTranspose_tensor, Matrix.conjTranspose_one]

private theorem original_diffusion_matrix (n : Nat) :
    (diffusionCircuit n).matrix =
      (initialPreparationCircuit n).matrix *
        (ZeroReflection.zeroReflectionOperator n *
          (initialPreparationCircuit n).matrix.dagger) := by
  apply Subtype.ext
  calc
    _ = (diffusionOperator n : HilbertOperator (Qubits n)) := diffusionCircuit_matrix n
    _ = ((diffusionElementaryCircuit n).matrix : HilbertOperator (Qubits n)) := by
      symm
      apply HilbertOperator.ext_of_applyVec_eq
      intro state
      simpa only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec] using
        diffusionElementaryCircuit_applyVec n state
    _ = _ := by
      simp only [diffusionElementaryCircuit, UnitaryCircuit.seq_matrix,
        UnitaryCircuit.dagger_matrix]
      change _ = (initialPreparationCircuit n).matrix.val *
        ((ZeroReflection.zeroReflectionOperator n).val *
          (initialPreparationCircuit n).matrix.dagger.val)
      rw [UnitaryOperator.coe_dagger]
      exact mul_assoc _ _ _

theorem diffusion_matrix (n k : Nat) (nonzero : k ≠ 0) :
    (diffusion n k nonzero).matrix = UnitaryOperator.tensor (diffusionCircuit n).matrix
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  have combine (suffix : Nat) :
      let originalH : HilbertOperator (Qubits n) := (initialPreparationCircuit n).matrix.val
      let originalS : HilbertOperator (Qubits n) := (ZeroReflection.zeroReflectionOperator n).val
      let originalD : HilbertOperator (Qubits n) := (initialPreparationCircuit n).matrix.dagger.val
      let actualH : HilbertOperator (Qubits (n + suffix)) := HilbertOperator.tensor originalH 1
      let actualS : HilbertOperator (Qubits (n + suffix)) := HilbertOperator.tensor originalS 1
      let actualD : HilbertOperator (Qubits (n + suffix)) := HilbertOperator.tensor originalD 1
      (actualH * actualS) * actualD =
        HilbertOperator.tensor (originalH * (originalS * originalD))
          (1 : HilbertOperator (Qubits suffix)) := by
    dsimp only
    rw [HilbertOperator.tensor_mul_tensor, one_mul, HilbertOperator.tensor_mul_tensor, one_mul,
      mul_assoc]
  apply Subtype.ext
  rw [diffusion, UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix,
    hadamards_matrix, reflection_matrix, hadamards_dagger_matrix, original_diffusion_matrix]
  exact combine (helperWidth n k)

theorem step_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) (nonzero : k ≠ 0) :
    (step marked k nonzero).matrix = UnitaryOperator.tensor (groverStepCircuit marked).matrix
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  apply Subtype.ext
  rw [step, UnitaryCircuit.seq_matrix, oracle_matrix, diffusion_matrix]
  change HilbertOperator.tensor
      ((diffusionCircuit n).matrix : HilbertOperator (Qubits n))
      (1 : HilbertOperator (Qubits (helperWidth n k))) *
    HilbertOperator.tensor
      ((phaseOracleCircuit marked).matrix : HilbertOperator (Qubits n)) 1 =
    HilbertOperator.tensor
      ((diffusionCircuit n).matrix.val * (phaseOracleCircuit marked).matrix.val) 1
  rw [HilbertOperator.tensor_mul_tensor, one_mul]

private theorem repeated_step_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (k : Nat) (nonzero : k ≠ 0) (repetitions : Nat) :
    (step marked k nonzero).matrix ^ repetitions =
      UnitaryOperator.tensor ((groverStepCircuit marked).matrix ^ repetitions)
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  induction repetitions with
  | zero =>
      apply Subtype.ext
      exact HilbertOperator.one_tensor_one.symm
  | succ repetitions ih =>
      rw [pow_succ, ih, step_matrix]
      apply Subtype.ext
      change HilbertOperator.tensor
          (((groverStepCircuit marked).matrix : HilbertOperator (Qubits n)) ^ repetitions)
          (1 : HilbertOperator (Qubits (helperWidth n k))) *
        HilbertOperator.tensor
          ((groverStepCircuit marked).matrix : HilbertOperator (Qubits n)) 1 =
        HilbertOperator.tensor
          (((groverStepCircuit marked).matrix : HilbertOperator (Qubits n)) ^ (repetitions + 1)) 1
      rw [HilbertOperator.tensor_mul_tensor, one_mul, pow_succ]

private theorem body_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (body marked k).matrix = UnitaryOperator.tensor (GroverSearch.circuit marked k).matrix
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  by_cases zero : k = 0
  · subst k
    rw [body, dif_pos rfl, hadamards_matrix]
    congr 1
    apply Subtype.ext
    rw [GroverSearch.circuit, UnitaryCircuit.seq_matrix,
      UnitaryCircuit.iterate_matrix, pow_zero, one_mul]
  · rw [body, dif_neg zero]
    apply Subtype.ext
    rw [UnitaryCircuit.seq_matrix, hadamards_matrix]
    have repeated :
        ((UnitaryCircuit.iterate k (step marked k zero)).matrix :
          HilbertOperator (Qubits (totalQubits n k))) =
        (UnitaryOperator.tensor ((groverStepCircuit marked).matrix ^ k)
          (1 : UnitaryOperator (Qubits (helperWidth n k)))).val :=
      congrArg Subtype.val (repeated_step_matrix marked k zero k)
    rw [repeated]
    change HilbertOperator.tensor
        (((groverStepCircuit marked).matrix : HilbertOperator (Qubits n)) ^ k)
        (1 : HilbertOperator (Qubits (helperWidth n k))) *
      HilbertOperator.tensor
        ((initialPreparationCircuit n).matrix : HilbertOperator (Qubits n)) 1 =
      HilbertOperator.tensor
        ((((groverStepCircuit marked).matrix : HilbertOperator (Qubits n)) ^ k) *
          (initialPreparationCircuit n).matrix.val) 1
    rw [HilbertOperator.tensor_mul_tensor, one_mul]

/-- The actual complete circuit equals the original full Grover operator and identity on work. -/
theorem circuit_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (circuit marked k).matrix = UnitaryOperator.tensor (GroverSearch.circuit marked k).matrix
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  apply Subtype.ext
  rw [circuit, UnitaryCircuit.seq_matrix, UnitaryCircuit.identity_matrix, one_mul, body_matrix]

/-- The internally prepared source and work values, both zero. -/
def inputVector (n k : Nat) : NormalizedVector (Qubits (totalQubits n k)) :=
  (inputState n).normalized.tensor (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)

/-- The original evolved Grover vector retains the same internally prepared work value. -/
def evolvedVector {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    NormalizedVector (Qubits (totalQubits n k)) :=
  (evolvedState marked k).normalized.tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)

/-- Actual execution on the internally prepared vector gives the original search state and work. -/
theorem circuit_applyNormalized_input {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (circuit marked k).applyNormalized (inputVector n k) = evolvedVector marked k := by
  change (circuit marked k).matrix.apply
      ((inputState n).normalized.tensor
        (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)) = _
  rw [circuit_matrix, UnitaryOperator.tensor_apply_tensor]
  have workFixed :
      (1 : UnitaryOperator (Qubits (helperWidth n k))).apply
          (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0) =
        NormalizedVector.ket (R := Qubits (helperWidth n k)) 0 := by
    apply NormalizedVector.ext
    intro index
    exact congrArg (fun state : HilbertVector (Qubits (helperWidth n k)) => state index)
      (UnitaryOperator.one_applyVec
        (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0).vec)
  rw [workFixed]
  rfl

end

end QuantumAlg.GroverSearch.Elementary
