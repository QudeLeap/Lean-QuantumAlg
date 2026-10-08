/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Grover.Elementary.Matrix
import all QuantumAlg.Algorithms.Grover.Construction
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact original Grover state from native execution

The native word's full matrix equals the independent predicate diffusion
operator. Its action on the prepared source/work vector is therefore the
original evolved search state with the same zero work value. Full matrix
agreement preserves arbitrary spectator correlations before preparation.
-/

namespace QuantumAlg.GroverSearch.Elementary

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

private theorem sourceStep_eq_diffusion {n : Nat} (marked : Fin (2 ^ n) → Bool) :
    sourceStep marked = diffusionOperator n * phaseOracleOp marked := by
  have reflected :
      (WalshHadamard.hadamardLayerOperator n * ZeroReflection.zeroReflectionOperator n) *
        star (WalshHadamard.hadamardLayerOperator n) = diffusionOperator n := by
    rw [mul_assoc]
    apply Subtype.ext
    apply HilbertOperator.ext_of_applyVec_eq
    intro state
    exact diffusionDecomposition_applyVec n state
  rw [sourceStep, reflected]

/-- The actual full native matrix is the original Grover evolution and identity on work. -/
theorem circuit_matrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    (circuit marked k).binaryMatrix = (sourceOperator marked k).tensor
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [circuit_binaryMatrix, sourceStep_eq_diffusion]
  rfl

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
    (circuit marked k).binaryMatrix.apply (inputVector n k) = evolvedVector marked k := by
  change (circuit marked k).binaryMatrix.apply
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
