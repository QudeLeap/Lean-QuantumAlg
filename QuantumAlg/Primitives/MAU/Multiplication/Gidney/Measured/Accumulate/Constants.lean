/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Util.Nat.FixedWidth.Modular.Accumulate

/-!
# Exact static positive and negative modular weights of the actual MAC words

Both source-order programs use canonical static residues. Their finite-word
conversion retains the exact natural value and does not execute a runtime
constant lookup [VBE95, 9511018.tex:333-367; G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

variable {width : Nat}

/-- The forward row's emitted finite constant is the original independently constructed residue. -/
lemma forwardConstant_nat (modulus : BitVec width) (coefficient : Nat) (index : Fin width)
    (positive : 0 < modulus.toNat) :
    (forwardConstant modulus coefficient index).toNat =
      Nat.FixedWidth.ModularAccumulate.stageConstantResidue
        modulus.toNat coefficient index.val := by
  rw [forwardConstant, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((Nat.FixedWidth.ModularAccumulate.stageConstantResidue_lt positive).trans
      modulus.isLt)]

/-- Every actual forward row constant is a canonical modular offset. -/
lemma forwardConstant_canonical (modulus : BitVec width) (coefficient : Nat) (index : Fin width)
    (positive : 0 < modulus.toNat) :
    (forwardConstant modulus coefficient index).toNat < modulus.toNat := by
  rw [forwardConstant_nat modulus coefficient index positive]
  exact Nat.FixedWidth.ModularAccumulate.stageConstantResidue_lt positive

/-- The separate inverse word emits exactly the canonical negative residue. -/
lemma inverseConstant_nat (modulus : BitVec width) (coefficient : Nat) (index : Fin width)
    (positive : 0 < modulus.toNat) :
    (inverseConstant modulus coefficient index).toNat =
      (modulus.toNat - Nat.FixedWidth.ModularAccumulate.stageConstantResidue
        modulus.toNat coefficient index.val) % modulus.toNat := by
  rw [inverseConstant, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ positive).trans modulus.isLt)]

/-- Every actual explicit inverse row constant is a canonical modular offset. -/
lemma inverseConstant_canonical (modulus : BitVec width) (coefficient : Nat) (index : Fin width)
    (positive : 0 < modulus.toNat) :
    (inverseConstant modulus coefficient index).toNat < modulus.toNat := by
  rw [inverseConstant_nat modulus coefficient index positive]
  exact Nat.mod_lt _ positive

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
