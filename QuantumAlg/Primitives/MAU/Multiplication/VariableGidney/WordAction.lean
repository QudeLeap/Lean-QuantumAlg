/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Util.FinPow
public import QuantumAlg.Util.Nat.FixedWidth.VariableWord.Equiv
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Nat.FixedWidth.VariableWord.Equiv

/-!
# Independent full-state variable modular-product target

The total finite permutation preserves both inputs and adds their product
to every canonical target; it fixes noncanonical target labels. This
operator is defined entirely from finite arithmetic, without an executor,
circuit witness, placement or resource estimate.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

open Nat.FixedWidth

/-- Join the three independent words in their original order. -/
public def wordLabelEquiv (width : Nat) :
    (Fin (2 ^ width) × (Fin (2 ^ width) × Fin (2 ^ width))) ≃
      Fin (2 ^ (width + (width + width))) :=
  (Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := width) (n := width))).trans
    (prodEquiv (m := width) (n := width + width))

private def labelAction (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    Equiv.Perm (Fin (2 ^ (width + (width + width)))) :=
  (wordLabelEquiv width).symm |>.trans (variableTripleEquiv modulus) |>.trans (wordLabelEquiv width)

/-- Independent exact quantum target on all three words. -/
public def wordVariableOperator (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryOperator (Qubits (width + (width + width))) :=
  UnitaryOperator.ofPerm (labelAction width modulus).symm

/-- The mathematical operator has the exact all-label arithmetic action and unit phase. -/
theorem wordVariableOperator_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (first second target : Fin (2 ^ width)) :
    (wordVariableOperator width modulus).apply
        (NormalizedVector.ket (wordLabelEquiv width (first, second, target))) =
      NormalizedVector.ket (R := Qubits (width + (width + width)))
        (wordLabelEquiv width
          (first, second, variableWordPrefix modulus first second target width)) := by
  rw [wordVariableOperator, UnitaryOperator.ofPerm_apply_ket]
  apply congrArg NormalizedVector.ket
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm, labelAction, Equiv.trans_apply,
    Equiv.symm_apply_apply, variableTripleEquiv_apply]

end

end QuantumAlg.MAU.Multiplication.VariableGidney
