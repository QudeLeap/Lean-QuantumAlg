/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Mathematical predicate phase operator

The predicate multiplies each marked basis vector by minus one and leaves
all other basis vectors fixed [dW19, qcnotes.tex:2769-2774]. The certified
operator is independent of the query access granted to an executable model.
-/

namespace QuantumAlg

noncomputable section

/-- The concrete diagonal phase-oracle operator, certified independently of
implementation metadata. -/
public def phaseOracleOp {n : Nat} (marked : Fin (2 ^ n) -> Bool) :
    UnitaryOperator (Qubits n) :=
  let op : HilbertOperator (Qubits n) :=
    fun i j => if i = j then (if marked j then -1 else 1 : ℂ) else 0
  UnitaryOperator.ofMatrix op
    (by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      rw [Matrix.mul_apply]
      by_cases hij : i = j
      · subst j
        by_cases hm : marked i <;>
          simp [op, Matrix.conjTranspose, Matrix.transpose, hm]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [op, Matrix.conjTranspose, Matrix.transpose, hij, hji])

theorem phaseOracle_apply_ket {n : Nat}
    (marked : Fin (2 ^ n) -> Bool) (j : Fin (2 ^ n)) :
    ((phaseOracleOp marked).apply (NormalizedVector.ket (R := Qubits n) j) :
        HilbertVector (Qubits n)) =
      ((if marked j then -1 else 1 : ℂ) •
        (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n))) := by
  by_cases hm : marked j
  · rw [if_pos hm]
    simp only [neg_smul, one_smul]
    apply WithLp.ofLp_injective
    funext i
    rw [show (((phaseOracleOp marked).apply
            (NormalizedVector.ket (R := Qubits n) j) : HilbertVector (Qubits n))).ofLp i =
          (phaseOracleOp marked).applyVec
            (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) i from rfl,
      show ((-(NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n))).ofLp i) =
          (-(NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n))) i from rfl,
      UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracleOp, UnitaryOperator.ofMatrix, hm,
        NormalizedVector.ket_apply]
    · simp [phaseOracleOp, UnitaryOperator.ofMatrix,
        NormalizedVector.ket_apply, hij]
  · rw [if_neg hm]
    simp only [one_smul]
    apply WithLp.ofLp_injective
    funext i
    rw [show (((phaseOracleOp marked).apply
            (NormalizedVector.ket (R := Qubits n) j) : HilbertVector (Qubits n))).ofLp i =
          (phaseOracleOp marked).applyVec
            (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) i from rfl,
      show ((NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)).ofLp i) =
          (NormalizedVector.ket (R := Qubits n) j : HilbertVector (Qubits n)) i from rfl,
      UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    by_cases hij : i = j
    · subst i
      simp [phaseOracleOp, UnitaryOperator.ofMatrix, hm,
        NormalizedVector.ket_apply]
    · simp [phaseOracleOp, UnitaryOperator.ofMatrix,
        NormalizedVector.ket_apply, hij]


end

end QuantumAlg
