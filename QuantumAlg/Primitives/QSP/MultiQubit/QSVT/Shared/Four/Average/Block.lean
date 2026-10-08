/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average

/-!
# The standard block-encoding coordinates of the three-ancilla average

Reassociation changes only the grouping of the original binary labels. It
does not permute physical wires, add gates, or add source-ancilla assumptions.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private def threeAssocEquiv (m n : Nat) :
    Fin (2 ^ (1 + (1 + (1 + (m + n))))) ≃ Fin (2 ^ ((1 + (1 + (1 + m))) + n)) :=
  finCongr (by simp only [Nat.add_assoc])

/-- Group the three transformation ancillas with the original block ancillas. -/
def reassociateThree {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (1 + (1 + (m + n)))))) :
    UnitaryOperator (Qubits ((1 + (1 + (1 + m))) + n)) :=
  UnitaryOperator.reindex (threeAssocEquiv m n) V

private theorem threeAssoc_zero (m n : Nat) (source : Fin (2 ^ n)) :
    (threeAssocEquiv m n).symm (prodEquiv ((0 : Fin (2 ^ (1 + (1 + (1 + m))))), source)) =
      prodEquiv ((0 : Fin 2), prodEquiv ((0 : Fin 2), prodEquiv ((0 : Fin 2),
        prodEquiv ((0 : Fin (2 ^ m)), source)))) := by
  apply Fin.ext
  simp [threeAssocEquiv, prodEquiv, finProdFinEquiv, finCongr]

/-- Standard zero-ancilla projection reads exactly the original three zero prefix coordinates. -/
theorem reassociateThree_projected_block {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (1 + (1 + (m + n)))))) :
    projectedBlock (1 + (1 + (1 + m))) n (reassociateThree V) =
      projectedBlock m n (ancillaBlock 0 0 (ancillaBlock 0 0 (ancillaBlock 0 0 V))) := by
  ext row column
  change V ((threeAssocEquiv m n).symm (prodEquiv (0, row)))
    ((threeAssocEquiv m n).symm (prodEquiv (0, column))) =
      V (prodEquiv (0, prodEquiv (0, prodEquiv (0, prodEquiv (0, row)))))
        (prodEquiv (0, prodEquiv (0, prodEquiv (0, prodEquiv (0, column)))))
  rw [threeAssoc_zero, threeAssoc_zero]

/-- The standard source-ancilla block is the average of the four independently specified blocks. -/
theorem threeAverage_projected_block {m n : Nat}
    (A B C D : UnitaryOperator (Qubits (1 + (m + n)))) :
    projectedBlock (1 + (1 + (1 + m))) n (reassociateThree (threeAverage A B C D)) =
      (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock A) +
      (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock B) +
        ((1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock C) +
          (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock D)) := by
  rw [reassociateThree_projected_block, threeAverage_zero_block]
  ext row column
  simp only [projectedBlock, Matrix.add_apply, Matrix.smul_apply]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
