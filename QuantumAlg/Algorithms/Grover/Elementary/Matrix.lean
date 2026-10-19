/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Grover.Elementary.Construction
import all QuantumAlg.Primitives.WalshHadamard.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
import all QuantumAlg.Core.Base.Gate.Unitary.Adjoint
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Full operator of Grover's native word

The actual phase query, inverse Hadamard word and exact positive zero
reflection realize the original Grover product on the complete source
space, tensored with identity on the retained helper. These are full matrix
equalities; no particular helper value or absence of correlations is assumed.
-/

namespace QuantumAlg.GroverSearch.Elementary

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- The independent source product: phase query, inverse H, positive zero reflection, H. -/
def sourceStep {n : Nat} (marked : Fin (2 ^ n) → Bool) : UnitaryOperator (Qubits n) :=
  (WalshHadamard.hadamardLayerOperator n * ZeroReflection.zeroReflectionOperator n) *
    star (WalshHadamard.hadamardLayerOperator n) * phaseOracleOp marked

lemma hadamards_binaryMatrix (queries : OracleModel)
    {environment : queries.Interpretation} (n k : Nat) :
    ((hadamards queries n k).binaryMatrix environment) =
      (WalshHadamard.hadamardLayerOperator n).tensor
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [hadamards, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  exact congrArg (fun operator : UnitaryOperator (Qubits n) =>
    operator.tensor (1 : UnitaryOperator (Qubits (helperWidth n k))))
    (WalshHadamard.Native.native_binary_matrix queries n environment)

lemma inverseHadamards_binaryMatrix (queries : OracleModel)
    {environment : queries.Interpretation} (n k : Nat) :
    ((inverseHadamards queries n k).binaryMatrix environment) =
      (star (WalshHadamard.hadamardLayerOperator n)).tensor
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  have inverse : ((inverseHadamards queries n k).binaryMatrix environment) =
      star ((hadamards .empty n k).binaryMatrix OracleModel.emptyInterpretation) := by
    rw [inverseHadamards, UnitaryCircuit.binaryMatrix, UnitaryCircuit.dagger_matrix,
      UnitaryOperator.unitaryOperator_reindex_star]
    rfl
  rw [inverse, hadamards_binaryMatrix]
  apply Subtype.ext
  change (HilbertOperator.tensor
    (WalshHadamard.hadamardLayerOperator n : HilbertOperator (Qubits n))
    (1 : HilbertOperator (Qubits (helperWidth n k)))).conjTranspose =
      HilbertOperator.tensor
        (WalshHadamard.hadamardLayerOperator n : HilbertOperator (Qubits n)).conjTranspose 1
  rw [HilbertOperator.conjTranspose_tensor, Matrix.conjTranspose_one]

lemma oracle_binaryMatrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ((oracle n k).binaryMatrix (interpretation marked)) = (phaseOracleOp marked).tensor
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [oracle, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits n) =>
    operator.tensor (1 : UnitaryOperator (Qubits (helperWidth n k))))
  rw [UnitaryCircuit.binaryMatrix, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm (phaseOracleOp marked)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm (phaseOracleOp marked)

lemma step_binaryMatrix {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (k : Nat) (nonzero : k ≠ 0) :
    ((step n k nonzero).binaryMatrix (interpretation marked)) = (sourceStep marked).tensor
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [step, diffusion, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    hadamards_binaryMatrix, inverseHadamards_binaryMatrix, oracle_binaryMatrix, reflection_matrix]
  apply Subtype.ext
  change (HilbertOperator.tensor
      (WalshHadamard.hadamardLayerOperator n : HilbertOperator (Qubits n))
      (1 : HilbertOperator (Qubits (helperWidth n k))) *
    (HilbertOperator.tensor
        (ZeroReflection.zeroReflectionOperator n : HilbertOperator (Qubits n))
        (1 : HilbertOperator (Qubits (helperWidth n k))) *
      HilbertOperator.tensor
        (star (WalshHadamard.hadamardLayerOperator n) : HilbertOperator (Qubits n))
        (1 : HilbertOperator (Qubits (helperWidth n k))))) *
      HilbertOperator.tensor (phaseOracleOp marked : HilbertOperator (Qubits n))
        (1 : HilbertOperator (Qubits (helperWidth n k))) =
      HilbertOperator.tensor
        ((((WalshHadamard.hadamardLayerOperator n : HilbertOperator (Qubits n)) *
          (ZeroReflection.zeroReflectionOperator n : HilbertOperator (Qubits n))) *
            (star (WalshHadamard.hadamardLayerOperator n) : HilbertOperator (Qubits n))) *
              (phaseOracleOp marked : HilbertOperator (Qubits n)))
        (1 : HilbertOperator (Qubits (helperWidth n k)))
  rw [HilbertOperator.tensor_mul_tensor, one_mul, HilbertOperator.tensor_mul_tensor, one_mul,
    HilbertOperator.tensor_mul_tensor, one_mul]
  simp only [mul_assoc]


private lemma repeated_step_binaryMatrix {n : Nat} (marked : Fin (2 ^ n) → Bool)
    (k : Nat) (nonzero : k ≠ 0) (count : Nat) :
    ((step n k nonzero).binaryMatrix (interpretation marked)) ^ count =
      (sourceStep marked ^ count).tensor
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  induction count with
  | zero =>
      apply Subtype.ext
      exact HilbertOperator.one_tensor_one.symm
  | succ count ih =>
      rw [pow_succ, ih, step_binaryMatrix]
      apply Subtype.ext
      change HilbertOperator.tensor
          ((sourceStep marked : HilbertOperator (Qubits n)) ^ count)
          (1 : HilbertOperator (Qubits (helperWidth n k))) *
        HilbertOperator.tensor (sourceStep marked : HilbertOperator (Qubits n)) 1 =
          HilbertOperator.tensor
            ((sourceStep marked : HilbertOperator (Qubits n)) ^ (count + 1)) 1
      rw [HilbertOperator.tensor_mul_tensor, one_mul, pow_succ]

/-- Exact native execution equals the complete original source product at every k. -/
lemma circuit_binaryMatrix {n : Nat} (marked : Fin (2 ^ n) → Bool) (k : Nat) :
    ((circuit n k).binaryMatrix (interpretation marked)) =
      (sourceStep marked ^ k * WalshHadamard.hadamardLayerOperator n).tensor
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  by_cases zero : k = 0
  · subst k
    rw [circuit, dif_pos rfl, hadamards_binaryMatrix, pow_zero, one_mul]
  · rw [circuit, dif_neg zero,
      UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
      UnitaryCircuit.unitaryCircuit_binaryMatrix_iterate,
      repeated_step_binaryMatrix, hadamards_binaryMatrix]
    apply Subtype.ext
    change HilbertOperator.tensor ((sourceStep marked : HilbertOperator (Qubits n)) ^ k)
        (1 : HilbertOperator (Qubits (helperWidth n k))) *
      HilbertOperator.tensor
        (WalshHadamard.hadamardLayerOperator n : HilbertOperator (Qubits n)) 1 =
        HilbertOperator.tensor _ 1
    rw [HilbertOperator.tensor_mul_tensor, one_mul]
    rfl

end

end QuantumAlg.GroverSearch.Elementary
