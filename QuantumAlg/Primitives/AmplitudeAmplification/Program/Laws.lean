/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Program
import all QuantumAlg.Primitives.AmplitudeAmplification.Model
import all QuantumAlg.Primitives.AmplitudeAmplification.Construction
import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Components.Oracle.AmplitudeAmplification.Circuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact action of the actual elementary amplification program

The whole program has the source-good-reflection operator tensor identity
on every work value. On the actually prepared source input it gives the
original all-k plane state, retaining the same zero work state. No equality
between the two reflection conventions outside their invariant plane is used.
-/

namespace QuantumAlg.AmplitudeAmplification.Native

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- The independent mathematical source iterate with the distinguishing good reflection. -/
def stepOperator {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) : UnitaryOperator (Qubits n) :=
  U * (ZeroReflection.zeroReflectionOperator n *
    (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good))

lemma preparation_matrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (preparation n k).binaryMatrix (interpretation U good) =
      UnitaryOperator.tensor (U)
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [preparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits n) =>
    operator.tensor (1 : UnitaryOperator (Qubits (helperWidth n k))))
  unfold UnitaryCircuit.binaryMatrix
  rw [AmplitudeAmplificationSource.Circuit.program_matrix]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm (U)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm (U)

lemma inversePreparation_matrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (inversePreparation n k).binaryMatrix (interpretation U good) =
      UnitaryOperator.tensor (U.dagger)
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [inversePreparation, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits n) =>
    operator.tensor (1 : UnitaryOperator (Qubits (helperWidth n k))))
  unfold UnitaryCircuit.binaryMatrix
  rw [AmplitudeAmplificationSource.Circuit.program_matrix]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm (U.dagger)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm (U.dagger)

lemma goodReflection_matrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (goodReflection n k).binaryMatrix (interpretation U good) =
      UnitaryOperator.tensor (OrthogonalProjector.rankOnePhaseReflectionOp good)
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  rw [goodReflection, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix]
  apply congrArg (fun operator : UnitaryOperator (Qubits n) =>
    operator.tensor (1 : UnitaryOperator (Qubits (helperWidth n k))))
  unfold UnitaryCircuit.binaryMatrix
  rw [AmplitudeAmplificationSource.Circuit.program_matrix]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm
      (OrthogonalProjector.rankOnePhaseReflectionOp good)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv n).symm (OrthogonalProjector.rankOnePhaseReflectionOp good)

lemma step_matrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) (nonzero : k ≠ 0) :
    (step n k nonzero).binaryMatrix (interpretation U good) =
      UnitaryOperator.tensor (stepOperator U good)
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  have combine (suffix : Nat) :
      let initial : HilbertOperator (Qubits n) := U.val
      let zero : HilbertOperator (Qubits n) := (ZeroReflection.zeroReflectionOperator n).val
      let inverse : HilbertOperator (Qubits n) := U.dagger.val
      let recognize : HilbertOperator (Qubits n) :=
        (OrthogonalProjector.rankOnePhaseReflectionOp good).val
      let actualInitial : HilbertOperator (Qubits (n + suffix)) :=
        HilbertOperator.tensor initial 1
      let actualZero : HilbertOperator (Qubits (n + suffix)) := HilbertOperator.tensor zero 1
      let actualInverse : HilbertOperator (Qubits (n + suffix)) :=
        HilbertOperator.tensor inverse 1
      let actualRecognize : HilbertOperator (Qubits (n + suffix)) :=
        HilbertOperator.tensor recognize 1
      actualInitial * (actualZero * (actualInverse * actualRecognize)) =
        HilbertOperator.tensor (initial * (zero * (inverse * recognize)))
          (1 : HilbertOperator (Qubits suffix)) := by
    dsimp only
    rw [HilbertOperator.tensor_mul_tensor, one_mul,
      HilbertOperator.tensor_mul_tensor, one_mul, HilbertOperator.tensor_mul_tensor, one_mul]
  apply Subtype.ext
  rw [step, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    preparation_matrix, inversePreparation_matrix, goodReflection_matrix,
    ZeroReflection.Workspace.reflection_matrix]
  exact combine (helperWidth n k)

private lemma repeated_step_matrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) (nonzero : k ≠ 0) (count : Nat) :
    (step n k nonzero).binaryMatrix (interpretation U good) ^ count =
      UnitaryOperator.tensor ((stepOperator U good) ^ count)
        (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  induction count with
  | zero =>
      apply Subtype.ext
      exact HilbertOperator.one_tensor_one.symm
  | succ count ih =>
      rw [pow_succ, ih, step_matrix]
      apply Subtype.ext
      change HilbertOperator.tensor
          (((stepOperator U good) : HilbertOperator (Qubits n)) ^ count)
          (1 : HilbertOperator (Qubits (helperWidth n k))) *
        HilbertOperator.tensor ((stepOperator U good) : HilbertOperator (Qubits n)) 1 =
        HilbertOperator.tensor
          (((stepOperator U good) : HilbertOperator (Qubits n)) ^ (count + 1)) 1
      rw [HilbertOperator.tensor_mul_tensor, one_mul, pow_succ]

lemma program_matrix {n : Nat} (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (k : Nat) :
    (program n k).binaryMatrix (interpretation U good) =
      UnitaryOperator.tensor ((stepOperator U good) ^ k * U)
      (1 : UnitaryOperator (Qubits (helperWidth n k))) := by
  by_cases zero : k = 0
  · subst k
    rw [program, dif_pos rfl, preparation_matrix, pow_zero, one_mul]
  · rw [program, dif_neg zero]
    apply Subtype.ext
    rw [UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, preparation_matrix]
    rw [UnitaryCircuit.unitaryCircuit_binaryMatrix_iterate,
      repeated_step_matrix U good k zero k]
    change HilbertOperator.tensor
        (((stepOperator U good) : HilbertOperator (Qubits n)) ^ k)
        (1 : HilbertOperator (Qubits (helperWidth n k))) *
      HilbertOperator.tensor (U : HilbertOperator (Qubits n)) 1 =
      HilbertOperator.tensor
        ((((stepOperator U good) : HilbertOperator (Qubits n)) ^ k) * U.val) 1
    rw [HilbertOperator.tensor_mul_tensor, one_mul]

/-- The source and selected work systems are all actually prepared in the zero basis state. -/
def inputVector (n k : Nat) : NormalizedVector (Qubits (totalQubits n k)) :=
  (NormalizedVector.ket (R := Qubits n) 0).tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)

/-- The original source closed form and the same retained zero work value. -/
def outputVector {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    NormalizedVector (Qubits (totalQubits n k)) :=
  (M.amplifiedState k).tensor (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)

/-- The actual program produces the original precise state at every angle and iteration count. -/
lemma program_applyNormalized_input {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) :
    ((program n k).binaryMatrix (interpretation M.preparation M.good)).apply
      (inputVector n k) = outputVector M k := by
  change ((program n k).binaryMatrix (interpretation M.preparation M.good)).apply
    ((NormalizedVector.ket (R := Qubits n) 0).tensor
      (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0)) = _
  rw [program_matrix, UnitaryOperator.tensor_apply_tensor]
  have source : ((stepOperator M.preparation M.good) ^ k * M.preparation).apply
      (NormalizedVector.ket (R := Qubits n) 0) = M.amplifiedState k := by
    have actual : ((intrinsicGoodSourceStepOperator M) ^ k).apply
        (M.preparation.apply M.zeroKet) = M.amplifiedState k := by
      rw [M.prepared_eq_amplifiedState_zero]
      exact intrinsicGoodSourceStepOperator_pow_apply M k
    apply NormalizedVector.ext
    intro index
    change ((stepOperator M.preparation M.good) ^ k * M.preparation).applyVec
      (M.zeroKet : HilbertVector (Qubits n)) index = _
    rw [UnitaryOperator.mul_applyVec]
    exact congrArg (fun state : NormalizedVector (Qubits n) => state index) actual
  have work : (1 : UnitaryOperator (Qubits (helperWidth n k))).apply
      (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0) =
        NormalizedVector.ket (R := Qubits (helperWidth n k)) 0 := by
    apply NormalizedVector.ext
    intro index
    exact congrArg (fun state : HilbertVector (Qubits (helperWidth n k)) => state index)
      (UnitaryOperator.one_applyVec _)
  rw [source, work]
  rfl

end

end QuantumAlg.AmplitudeAmplification.Native
