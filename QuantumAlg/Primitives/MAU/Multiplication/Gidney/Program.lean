/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Swap
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Program
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Multiplication

/-!
# Unit multiplication by actual accumulation and adjoint cleanup

The two-word program performs an actual multiply-accumulate, the literal
word swap, and the adjoint of an actual inverse-coefficient accumulation.
Its total permutation is specified independently in finite arithmetic.
On a canonical input and a zero auxiliary word, the output is the unit
product and the auxiliary word is returned to zero. An arbitrary nonzero
auxiliary word instead follows the stated full two-word permutation.

This is the clean-auxiliary compute/uncompute specialization of the
unit-inverse arithmetic in [G17, paper.tex:186-211]. No odd-modulus condition
is introduced, and the unit equations include modulus one.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Accumulate.Gidney Nat.FixedWidth

private theorem accumulate_equiv (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    UnitaryCircuit.Realizes (encoding width)
      (Accumulate.Gidney.program width modulus coefficient)
      (accumulatePairEquiv modulus coefficient width) :=
  (gidneyAccumulate_realizes width modulus coefficient).congrStep
    (fun state => (accumulatePairEquiv_apply modulus coefficient width state).symm)

private theorem inverse_accumulate_equiv (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) :
    UnitaryCircuit.Realizes (encoding width)
      (Accumulate.Gidney.program width modulus coefficient).dagger
      (accumulatePairEquiv modulus coefficient width).symm :=
  (accumulate_equiv width modulus coefficient).dagger_of_rightInverse
    (Equiv.apply_symm_apply _)

/-- Actual MAC, three-CNOT word swaps, then the adjoint of the inverse-coefficient MAC. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryCircuit (Qubits (encoding width).width) :=
  ((Accumulate.Gidney.program width modulus (coefficient : ZMod modulus.val).val).seq
    (wordSwapProgram width)).seq
      (Accumulate.Gidney.program width modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val).dagger

/-- Exact action of the actual program on every two-word basis label, with no phase allowance. -/
theorem gidneyUnitMultiplication_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (encoding width) (program width modulus coefficient)
      (unitMultiplicationPairEquiv modulus coefficient) :=
  ((accumulate_equiv width modulus (coefficient : ZMod modulus.val).val).seq
    (gidneyWordSwap_realizes width)).seq
      (inverse_accumulate_equiv width modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val)

/-- The canonical product is computed while the zero auxiliary word is restored exactly. -/
theorem gidneyUnitMultiplication_clean (width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) (valid : input.val < modulus.val) :
    (program width modulus coefficient).applyNormalized
        (NormalizedVector.ket ((encoding width).encode (input, 0))) =
      NormalizedVector.ket ((encoding width).encode
        (unitProductWord modulus positive coefficient input, 0)) := by
  rw [(gidneyUnitMultiplication_realizes width modulus coefficient).apply_encoded_ket,
    unitMultiplicationPairEquiv_clean modulus positive coefficient input valid]

/-- The full physical footprint is precisely the two original words. -/
theorem gidneyUnitMultiplication_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (program width modulus coefficient).physical_idx = List.range (2 * width) := by
  have first : (Accumulate.Gidney.program width modulus
      (coefficient : ZMod modulus.val).val).physical_idx ⊆ List.range (2 * width) := by
    intro wire present
    rw [gidneyAccumulate_physical] at present
    exact present
  have before := UnitaryCircuit.seq_physical_idx_subset _ _ first (gidneyWordSwap_physical width)
  change ((Accumulate.Gidney.program width modulus
      (coefficient : ZMod modulus.val).val).seq (wordSwapProgram width)).physical_idx ∪
    (Accumulate.Gidney.program width modulus
      ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val).dagger.physical_idx = _
  rw [UnitaryCircuit.dagger_physical_idx, gidneyAccumulate_physical]
  exact before.union_eq_right

/-- The exact total two-word action preserves an arbitrary external encoded reference jointly. -/
theorem gidneyUnitMultiplication_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (UnitaryCircuit.prodLeft (n := reference.width) (program width modulus coefficient))
      (fun state => (unitMultiplicationPairEquiv modulus coefficient state.1, state.2)) :=
  (gidneyUnitMultiplication_realizes width modulus coefficient).prodLeft

end

end QuantumAlg.MAU.Multiplication.Gidney
