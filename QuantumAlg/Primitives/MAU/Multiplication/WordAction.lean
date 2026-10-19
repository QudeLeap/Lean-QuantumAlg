/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Util.FinPow
public import Mathlib.Data.ZMod.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Multiplication

/-!
# Independent complete two-word unit-multiplication operator

Finite arithmetic specifies the compute/swap/inverse-compute permutation.
Its action on a canonical input and a zero auxiliary word is multiplication
by the compiled residue unit with exact auxiliary restoration. The complete
operator also specifies every other two-word label independently of any
circuit or resource choice [G17, paper.tex:186-211].
-/

namespace QuantumAlg.MAU.Multiplication

noncomputable section

open Nat.FixedWidth

private def multiplicationLabelEquiv (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : Equiv.Perm (Fin (2 ^ (width + width))) :=
  (prodEquiv (m := width) (n := width)).symm |>.trans
    (unitMultiplicationPairEquiv modulus coefficient) |>.trans
      (prodEquiv (m := width) (n := width))

/-- The independent complete two-word operator has no circuit or resource metadata. -/
public def wordUnitMultiplicationOperator (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryOperator (Qubits (width + width)) :=
  UnitaryOperator.ofPerm (multiplicationLabelEquiv width modulus coefficient).symm

lemma wordUnitMultiplicationOperator_ket (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (state : Fin (2 ^ width) × Fin (2 ^ width)) :
    (wordUnitMultiplicationOperator width modulus coefficient).apply
        (NormalizedVector.ket (prodEquiv (m := width) (n := width) state)) =
      NormalizedVector.ket (R := Qubits (width + width))
        (prodEquiv (m := width) (n := width)
          (unitMultiplicationPairEquiv modulus coefficient state)) := by
  rw [wordUnitMultiplicationOperator, UnitaryOperator.ofPerm_apply_ket]
  apply congrArg NormalizedVector.ket
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm, multiplicationLabelEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply]

lemma wordUnitMultiplicationOperator_clean (width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) (valid : input.val < modulus.val) :
    (wordUnitMultiplicationOperator width modulus coefficient).apply
        (NormalizedVector.ket (prodEquiv (m := width) (n := width) (input, 0))) =
      NormalizedVector.ket (R := Qubits (width + width))
        (prodEquiv (m := width) (n := width)
          (unitProductWord modulus positive coefficient input, 0)) := by
  rw [wordUnitMultiplicationOperator_ket,
    unitMultiplicationPairEquiv_clean modulus positive coefficient input valid]

end

end QuantumAlg.MAU.Multiplication
