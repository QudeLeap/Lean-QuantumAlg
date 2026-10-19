/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Util.FinPow
public import QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Oracle
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Oracle
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-!
# Independent complete modular-exponentiation XOR operator

Pure finite arithmetic fixes the action on every exponent, power, auxiliary,
and arbitrary target label. The corresponding permutation operator contains
no circuit or resource metadata. On the compiled canonical work basis it
XORs the modular power into the target and restores both work words exactly
[VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation

noncomputable section

open Nat.FixedWidth

/-- Pack exponent, power, auxiliary, and target in that declared order. -/
public def wordExponentiationBasis (exponentWidth width : Nat) :
    ((Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width)) ≃
      (Qubits ((exponentWidth + (width + width)) + width)).Index :=
  (Equiv.prodCongr
    ((Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := width) (n := width))).trans
      (prodEquiv (m := exponentWidth) (n := width + width)))
    (Equiv.refl _)).trans (prodEquiv (m := exponentWidth + (width + width)) (n := width))

private def exponentiationPermutation (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    Equiv.Perm (Qubits ((exponentWidth + (width + width)) + width)).Index :=
  (wordExponentiationBasis exponentWidth width).symm |>.trans
    (unitPowerOracleEquiv exponentWidth width modulus base) |>.trans
      (wordExponentiationBasis exponentWidth width)

/-- The full finite XOR operator is specified without an implementation or resource projection. -/
public def wordExponentiationOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator (Qubits ((exponentWidth + (width + width)) + width)) :=
  UnitaryOperator.ofPerm (exponentiationPermutation exponentWidth width modulus base).symm

/-- Every basis label follows the independent total arithmetic action with exact phase. -/
public lemma wordExponentiationOperator_ket (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (state : (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) × Fin (2 ^ width)) :
    (wordExponentiationOperator exponentWidth width modulus base).apply
        (NormalizedVector.ket (wordExponentiationBasis exponentWidth width state)) =
      NormalizedVector.ket (R := Qubits ((exponentWidth + (width + width)) + width))
        (wordExponentiationBasis exponentWidth width
          (unitPowerOracleOutput modulus base state)) := by
  rw [wordExponentiationOperator, UnitaryOperator.ofPerm_apply_ket]
  apply congrArg NormalizedVector.ket
  simp only [Equiv.Perm.inv_def, Equiv.symm_symm, exponentiationPermutation,
    Equiv.trans_apply, Equiv.symm_apply_apply, unitPowerOracleEquiv_apply]

/-- The independent operator returns the canonical work basis for every arbitrary XOR target. -/
lemma wordExponentiationOperator_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (target : Fin (2 ^ width)) :
    (wordExponentiationOperator exponentWidth width modulus base).apply
        (NormalizedVector.ket (wordExponentiationBasis exponentWidth width
          ((exponent, unitResidueWord modulus positive 1, 0), target))) =
      NormalizedVector.ket (R := Qubits ((exponentWidth + (width + width)) + width))
        (wordExponentiationBasis exponentWidth width
          ((exponent, unitResidueWord modulus positive 1, 0),
            ⟨target.val ^^^ (unitResidueWord modulus positive (base ^ exponent.val)).val,
              Nat.xor_lt_two_pow target.isLt
                (unitResidueWord modulus positive (base ^ exponent.val)).isLt⟩)) := by
  rw [wordExponentiationOperator_ket, unitPowerOracleOutput_clean]

end

end QuantumAlg.MAU.Exponentiation
