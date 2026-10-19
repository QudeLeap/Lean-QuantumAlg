/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Exact action of the mathematical phase-controlled operator

A complete phase label selects its own source exponent. This matrix lemma
acts on arbitrary source vectors and leaves the entire phase ket unchanged;
it introduces no circuit, state promise or probability carrier.
-/

namespace QuantumAlg

noncomputable section

/-- A phase basis label selects the source exponent of the existing block-diagonal operator. -/
lemma qpeExponentOp_applyVec_ket_tensor {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (exponent : Fin (2 ^ t) → Nat)
    (phase : Fin (2 ^ t)) (target : HilbertVector (Qubits n)) :
    (qpeExponentOp t U exponent).applyVec
        (HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec target) =
      HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec
        ((U ^ exponent phase).applyVec target) := by
  apply WithLp.ofLp_injective
  funext row
  obtain ⟨⟨leftPhase, leftSource⟩, rfl⟩ := (prodEquiv (m := t) (n := n)).surjective row
  change (qpeExponentOp t U exponent).applyVec
      (HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec target)
        (prodEquiv (leftPhase, leftSource)) =
    HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec
      ((U ^ exponent phase).applyVec target) (prodEquiv (leftPhase, leftSource))
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_apply,
    HilbertVector.tensor_apply_prod, UnitaryOperator.applyVec, HilbertOperator.applyVec_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := t) (n := n))
    (fun column : Fin (2 ^ (t + n)) =>
      (qpeExponentOp t U exponent) (prodEquiv (leftPhase, leftSource)) column *
        HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec target column),
    Fintype.sum_prod_type]
  simp only [qpeExponentOp_apply, Equiv.symm_apply_apply, HilbertVector.tensor_apply_prod,
    NormalizedVector.ket_apply]
  by_cases equalPhase : leftPhase = phase
  · subst leftPhase
    simp [eq_comm]
  · simp [equalPhase, eq_comm]

/-- One selected phase bit either applies the source operator or preserves the full source. -/
lemma qpeControlledBitOp_applyVec_ket_tensor {n : Nat} (t : Nat)
    (U : UnitaryOperator (Qubits n)) (stage : Fin t)
    (phase : Fin (2 ^ t)) (target : HilbertVector (Qubits n)) :
    (qpeControlledBitOp t U stage).applyVec
        (HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec target) =
      HilbertVector.tensor (NormalizedVector.ket (R := Qubits t) phase).vec
        (if phase.val.testBit stage.val then U.applyVec target else target) := by
  rw [qpeControlledBitOp, qpeExponentOp_applyVec_ket_tensor]
  cases phase.val.testBit stage.val <;> simp [UnitaryOperator.one_applyVec]

end

end QuantumAlg
