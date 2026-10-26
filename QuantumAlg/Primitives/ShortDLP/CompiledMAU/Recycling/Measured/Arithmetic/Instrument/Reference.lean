/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Matrix
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Control

/-!
# Independent controlled-unit arithmetic matrix and untouched reference factor

The canonical unit translation and its control block specify the arithmetic
independently of the emitted measured native word. The exact reference
factorization retains every off-diagonal entry [G25, main.tex:354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open scoped Kronecker

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]

/-- Independent unit translation on the canonical modular-unit register. -/
def unitTranslation (coefficient : (ZMod modulus.toNat)ˣ) :
    UnitaryOperator (Recycling.Carrier.units modulus.toNat) :=
  UnitaryOperator.ofPerm (Equiv.mulLeft coefficient).symm

/-- The source controlled permutation is precisely the ordinary control block of multiplication. -/
lemma controlledAction_matrix (coefficient : (ZMod modulus.toNat)ˣ) :
    (UnitaryOperator.ofPerm (Carrier.controlledAction modulus coefficient).symm :
        HilbertOperator (Recycling.Carrier.full modulus.toNat)) =
      Recycling.ControlKraus.controlledBlock
        (unitTranslation modulus coefficient :
          HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  exact Recycling.ControlKraus.controlledAction_matrix
    (⟨modulus.toNat, Nat.lt_succ_of_lt modulus.isLt⟩ : Fin (2 ^ width + 1)) coefficient

/-- The complete logical source matrix acts as identity on every external-reference coordinate. -/
lemma arithmeticReference_matrix (coefficient : (ZMod modulus.toNat)ˣ) (Reference : Register) :
    (UnitaryOperator.ofPerm (arithmeticReferencePermutation modulus coefficient Reference).symm :
        HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference)) =
      (UnitaryOperator.ofPerm (Carrier.controlledAction modulus coefficient).symm :
        HilbertOperator (Recycling.Carrier.full modulus.toNat)) ⊗ₖ
          (1 : HilbertOperator Reference) := by
  classical
  ext row column
  rcases row with ⟨rowLocal, rowReference⟩
  rcases column with ⟨columnLocal, columnReference⟩
  have inverse : (arithmeticReferencePermutation modulus coefficient Reference).symm
      (rowLocal, rowReference) =
        ((Carrier.controlledAction modulus coefficient).symm rowLocal, rowReference) := rfl
  have pairs :
      (((Carrier.controlledAction modulus coefficient).symm rowLocal, rowReference) :
        ((Recycling.Carrier.full modulus.toNat).prod Reference).Index) =
          (columnLocal, columnReference) ↔
        (Carrier.controlledAction modulus coefficient).symm rowLocal = columnLocal ∧
          rowReference = columnReference := by
    constructor
    · intro same
      exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [UnitaryOperator.ofPerm_entry, Matrix.kronecker_apply, Matrix.one_apply,
    inverse, pairs]
  split_ifs <;> simp_all

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
