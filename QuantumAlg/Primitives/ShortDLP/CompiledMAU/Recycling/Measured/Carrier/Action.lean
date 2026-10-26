/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier

/-!
# Actual measured arithmetic as the original controlled unit translation

Only the canonical internally prepared unit carrier is compared with a
logical permutation. The full actual measured program and its separate
per-record scalar remain explicit; no measured instrument is replaced by
a unitary compiler [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Carrier

noncomputable section

open MAU.Multiplication.Gidney.Measured MAU.Addition.Gidney.Measured.Instruction

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]

/-- Independent controlled translation on both original control values and canonical unit seeds. -/
def controlledAction (coefficient : (ZMod modulus.toNat)ˣ) :
    Equiv.Perm (Recycling.Carrier.full modulus.toNat).Index :=
  Equiv.prodCongrRight fun bit => Equiv.mulLeft
    (if bit.val.testBit 0 then coefficient else 1)

/-- The complete physical word implements the original unit translation on its clean carrier. -/
lemma measuredWord_physicalLabel (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (label : (Recycling.Carrier.full modulus.toNat).Index) :
    wordLabel ((Physical.layout width).multiplicationWord wide modulus
      (coefficient : ZMod modulus.toNat).val
      ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
      (physicalLabel modulus label) =
        physicalLabel modulus (controlledAction modulus coefficient label) := by
  rw [physicalLabel, Physical.multiplicationWord_cleanLabel wide modulus positive coefficient
    (finTwoEquiv label.1) (unitWord modulus label.2) (unitWord_canonical modulus label.2),
    selectedProduct_unit modulus positive coefficient label.2 label.1]
  rfl

/-- Actual physical unit-carrier labels supply precisely the internally clean adder helpers. -/
lemma physicalLabel_helpers (label : (Recycling.Carrier.full modulus.toNat).Index) :
    ∀ helper, ((Physical.layout width).clean helper).get (physicalLabel modulus label) = false :=
  (Physical.cleanLabel_helpers width (finTwoEquiv label.1) (unitWord modulus label.2)).1

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Carrier
