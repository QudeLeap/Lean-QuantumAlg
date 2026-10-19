/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Multiplication
import Mathlib.Logic.Equiv.Prod

/-!
# Total reversible arithmetic for selected unit-power stages

The compiled exponent position selects either the exact two-word modular
unit permutation or the identity. Composing a static list gives a finite
equivalence with its own mathematical inverse, independently of any quantum
implementation [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.Nat.FixedWidth

noncomputable section

open QuantumAlg.Nat.FixedWidth.UnitExponentiation

/-- An exponent bit selects a unit multiplication on the other two words. -/
def unitPowerStageEquiv {exponentWidth width : Nat} (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth) :
    Equiv.Perm (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) :=
  Equiv.prodCongrRight fun exponent : Fin (2 ^ exponentWidth) =>
    if exponent.val.testBit bit.val then unitMultiplicationPairEquiv modulus (stageUnit base bit)
    else Equiv.refl _

lemma unitPowerStageEquiv_apply {exponentWidth width : Nat}
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) (bit : Fin exponentWidth)
    (state : Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width))) :
    unitPowerStageEquiv modulus base bit state =
      (state.1, if state.1.val.testBit bit.val then
        unitMultiplicationPairEquiv modulus (stageUnit base bit) state.2 else state.2) := by
  rcases state with ⟨exponent, words⟩
  unfold unitPowerStageEquiv
  rw [Equiv.prodCongrRight_apply]
  cases exponent.val.testBit bit.val <;> rfl

/-- Compose only the independently specified finite arithmetic equivalences. -/
def unitPowerBitsEquiv {exponentWidth width : Nat} (modulus : Fin (2 ^ width + 1))
    (base : (ZMod modulus.val)ˣ) :
    List (Fin exponentWidth) →
      Equiv.Perm (Fin (2 ^ exponentWidth) × (Fin (2 ^ width) × Fin (2 ^ width)))
  | [] => Equiv.refl _
  | bit :: bits => (unitPowerStageEquiv modulus base bit).trans
      (unitPowerBitsEquiv modulus base bits)

end

end QuantumAlg.Nat.FixedWidth
