/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Borrowed.Coordinates
import all QuantumAlg.Core.Execution.Borrowed.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Owned-word action with exact borrowed identity

Transport the tensor operator through coordinates derived from actual physical
positions. The resulting factorization is exactly the one required for joint
borrowed restoration; it has no input-state or reference-independence premise.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

def wordOperator (owned borrowed : Nat) (operator : UnitaryOperator (Qubits owned)) :
    UnitaryOperator (context owned borrowed).register :=
  UnitaryOperator.reindex (wordBinaryEquiv owned borrowed).symm
    (operator.tensor (1 : UnitaryOperator (Qubits borrowed)))

def complementaryOperator (owned borrowed : Nat) (operator : UnitaryOperator (Qubits owned)) :
    UnitaryOperator
      ((context owned borrowed).quantumLayout.complementRegister
        (context owned borrowed).borrowedSelection) :=
  UnitaryOperator.reindex (ownedBinaryEquiv owned borrowed).symm operator

private lemma wordBinaryEquiv_join (owned borrowed : Nat)
    (selected : (context owned borrowed).quantumLayout.SelectedBasis
      (context owned borrowed).borrowedSelection)
    (complement : (context owned borrowed).quantumLayout.ComplementBasis
      (context owned borrowed).borrowedSelection) :
    wordBinaryEquiv owned borrowed
      ((context owned borrowed).quantumLayout.joinSelectedBasis
        (context owned borrowed).borrowedSelection selected complement) =
      prodEquiv (ownedBinaryEquiv owned borrowed complement,
        borrowedBinaryEquiv owned borrowed selected) :=
  congrArg (prodEquiv (m := owned) (n := borrowed))
    (wordPairEquiv_join owned borrowed selected complement)

/-- The independent owned-word operator is exactly identity on the actual borrowed selection. -/
lemma wordOperator_complement (owned borrowed : Nat)
    (operator : UnitaryOperator (Qubits owned)) :
    UnitaryOperator.reindex
      ((context owned borrowed).quantumLayout.selectionBasisEquiv
        (context owned borrowed).borrowedSelection)
      (wordOperator owned borrowed operator) =
    UnitaryOperator.prodTensor
      (1 : UnitaryOperator ((context owned borrowed).quantumLayout.selectedRegister
        (context owned borrowed).borrowedSelection))
      (complementaryOperator owned borrowed operator) := by
  apply Subtype.ext
  ext row column
  change (operator.tensor (1 : UnitaryOperator (Qubits borrowed)))
      (wordBinaryEquiv owned borrowed
        ((context owned borrowed).quantumLayout.joinSelectedBasis
          (context owned borrowed).borrowedSelection row.1 row.2))
      (wordBinaryEquiv owned borrowed
        ((context owned borrowed).quantumLayout.joinSelectedBasis
          (context owned borrowed).borrowedSelection column.1 column.2)) = _
  rw [wordBinaryEquiv_join, wordBinaryEquiv_join, UnitaryOperator.tensor_apply]
  simp only [Equiv.symm_apply_apply]
  change operator (ownedBinaryEquiv owned borrowed row.2)
      (ownedBinaryEquiv owned borrowed column.2) *
        (if borrowedBinaryEquiv owned borrowed row.1 = borrowedBinaryEquiv owned borrowed column.1
          then (1 : ℂ) else 0) =
    (if row.1 = column.1 then 1 else 0) *
      operator (ownedBinaryEquiv owned borrowed row.2) (ownedBinaryEquiv owned borrowed column.2)
  by_cases same : row.1 = column.1
  · have sameEncoded := congrArg (borrowedBinaryEquiv owned borrowed) same
    simp only [if_pos same, if_pos sameEncoded, mul_one, one_mul]
  · have different : borrowedBinaryEquiv owned borrowed row.1 ≠
        borrowedBinaryEquiv owned borrowed column.1 :=
      fun equal => same ((borrowedBinaryEquiv owned borrowed).injective equal)
    simp only [if_neg same, if_neg different, mul_zero, zero_mul]

end

end QuantumAlg.Execution.OwnedBorrowedQubits
