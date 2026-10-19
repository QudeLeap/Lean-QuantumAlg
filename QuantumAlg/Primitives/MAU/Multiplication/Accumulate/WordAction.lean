/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Util.FinPow
public import QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Accumulate
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Equiv

/-!
# Independent reversible modular accumulation operator

Finite arithmetic alone specifies the complete two-word permutation. The
source is preserved; canonical target residues receive `a*x` modulo the
fitted modulus, and other target labels are fixed. The operator contains
no circuit, placement, resource ledger, or compilation choice.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate

noncomputable section

open Nat.FixedWidth

private def accumulationLabelEquiv (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : Equiv.Perm (Fin (2 ^ (width + width))) :=
  (prodEquiv (m := width) (n := width)).symm |>.trans
    (accumulatePairEquiv modulus coefficient width) |>.trans
      (prodEquiv (m := width) (n := width))

/-- Independent exact action on the complete two-word quantum carrier. -/
public def wordAccumulateOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : UnitaryOperator (Qubits (width + width)) :=
  UnitaryOperator.ofPerm (accumulationLabelEquiv width modulus coefficient).symm

/-- The independent permutation has the exact arithmetic basis action, with unit phase. -/
public lemma wordAccumulateOperator_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (source target : Fin (2 ^ width)) :
    (wordAccumulateOperator width modulus coefficient).apply
        (NormalizedVector.ket (prodEquiv (m := width) (n := width) (source, target))) =
      NormalizedVector.ket (R := Qubits (width + width))
        (prodEquiv (m := width) (n := width)
          (source, accumulateWordPrefix modulus coefficient source target width)) := by
  rw [wordAccumulateOperator, UnitaryOperator.ofPerm_apply_ket]
  apply congrArg NormalizedVector.ket
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm, accumulationLabelEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply, accumulatePairEquiv_apply]

end

end QuantumAlg.MAU.Multiplication.Accumulate
