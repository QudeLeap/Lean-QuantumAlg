/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of selected binary powers of a modular unit

A static power belongs to each exponent position. Multiplying exactly the
powers selected by the low bits reconstructs exponentiation by the binary
prefix. The full finite word gives the complete exponent. These identities
are independent of circuit storage and scheduling and apply to every modulus,
including one and even moduli [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.Nat.FixedWidth.UnitExponentiation

noncomputable section

/-- Static multiplier used at exponent position `bit`. -/
def stageUnit {m N : Nat} (u : (ZMod N)ˣ) (bit : Fin m) : (ZMod N)ˣ :=
  u ^ (2 ^ bit.val)

/-- Unit selected by one exponent bit. -/
def selectedUnit {m N : Nat} (u : (ZMod N)ˣ) (exponent : Nat)
    (bit : Fin m) : (ZMod N)ˣ :=
  if exponent.testBit bit.val then stageUnit u bit else 1

/-- Product of the static powers selected by a list of exponent wires. -/
def scheduledUnit {m N : Nat} (u : (ZMod N)ˣ) (exponent : Nat)
    (bits : List (Fin m)) : (ZMod N)ˣ :=
  (bits.map (selectedUnit u exponent)).prod

/-- Product over the first `m` selected powers is `u` raised to the low-`m`
binary prefix of the exponent. -/
theorem selectedUnit_product_eq_pow_selectedLowWeight
    {N : Nat} (m : Nat) (u : (ZMod N)ˣ) (exponent : Nat) :
    (∏ bit : Fin m, selectedUnit u exponent bit) =
      u ^ QuantumAlg.Nat.FixedWidth.ModularAccumulate.selectedLowWeight exponent m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Fin.prod_univ_castSucc,
        QuantumAlg.Nat.FixedWidth.ModularAccumulate.selectedLowWeight_succ,
        pow_add]
      have hprefix :
          (∏ bit : Fin m, selectedUnit u exponent bit.castSucc) =
            u ^ QuantumAlg.Nat.FixedWidth.ModularAccumulate.selectedLowWeight
              exponent m := by
        simpa [selectedUnit, stageUnit] using ih
      rw [hprefix]
      cases hbit : exponent.testBit m <;>
        simp [selectedUnit, stageUnit, hbit,
          QuantumAlg.Nat.FixedWidth.ModularAccumulate.selectedBitWeight]

/-- Scheduling every exponent wire selects exactly `u^exponent`. -/
theorem scheduledUnit_all_eq_pow {m N : Nat}
    (u : (ZMod N)ˣ) (exponent : Fin (2 ^ m)) :
    scheduledUnit u exponent.val (List.ofFn fun bit : Fin m => bit) =
      u ^ exponent.val := by
  unfold scheduledUnit
  rw [List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply]
  rw [
    selectedUnit_product_eq_pow_selectedLowWeight m u exponent.val,
    QuantumAlg.Nat.FixedWidth.ModularAccumulate.selectedLowWeight_eq_self_of_lt_two_pow
      exponent.isLt]

end

end QuantumAlg.Nat.FixedWidth.UnitExponentiation
