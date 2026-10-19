/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Swap
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Gates
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

variable {environment : OracleModel.empty.Interpretation}

open Accumulate.Gidney Nat.FixedWidth EncodedBit GateSpec

private lemma accumulateGates_equiv (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (state : Registers width) :
    stepList (Accumulate.Gidney.gates width modulus coefficient) state =
      accumulatePairEquiv modulus coefficient width state :=
  (gidneyAccumulateGates_step width modulus coefficient state).trans
    (accumulatePairEquiv_apply modulus coefficient width state).symm

private lemma inverseAccumulateGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) (state : Registers width) :
    stepList (Accumulate.Gidney.gates width modulus coefficient).reverse state =
      (accumulatePairEquiv modulus coefficient width).symm state := by
  have inverse := stepList_reverse_stepList (Accumulate.Gidney.gates width modulus coefficient)
    ((accumulatePairEquiv modulus coefficient width).symm state)
  rw [accumulateGates_equiv, Equiv.apply_symm_apply] at inverse
  exact inverse

/-- Actual MAC, three-CNOT word swaps, then reversed inverse-coefficient MAC instructions. -/
def gates (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : List (GateSpec (encoding width)) :=
  (Accumulate.Gidney.gates width modulus (coefficient : ZMod modulus.val).val ++
    wordSwapGates width) ++
      (Accumulate.Gidney.gates width modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val).reverse

/-- Every joint basis label follows the independent total multiplication permutation. -/
lemma gidneyUnitMultiplicationGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (state : Registers width) :
    stepList (gates width modulus coefficient) state =
      unitMultiplicationPairEquiv modulus coefficient state := by
  simp only [gates, stepList_append, accumulateGates_equiv,
    gidneyWordSwapGates_step, inverseAccumulateGates_step]
  rfl

/-- Emit the complete native instruction sequence on the original two words. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates width modulus coefficient)

/-- Exact action of the actual program on every two-word basis label, with no phase allowance. -/
lemma gidneyUnitMultiplication_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (encoding width) (program width modulus coefficient) environment
      (unitMultiplicationPairEquiv modulus coefficient) :=
  realizesList_congrStep _ _ _ (gidneyUnitMultiplicationGates_step width modulus coefficient)
      environment

/-- The canonical product is computed while the zero auxiliary word is restored exactly. -/
lemma gidneyUnitMultiplication_clean (width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) (valid : input.val < modulus.val) :
    (program width modulus coefficient).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
          ((encoding width).encode (input, 0)))) =
      NormalizedVector.ket ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
        ((encoding width).encode (unitProductWord modulus positive coefficient input, 0))) := by
  rw [(gidneyUnitMultiplication_realizes width modulus coefficient).apply_encoded_ket,
    unitMultiplicationPairEquiv_clean modulus positive coefficient input valid]

/-- The complete multiplication layout is the original two words. -/
lemma gidneyUnitMultiplication_interface (width : Nat) :
    (encoding width).width = 2 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (2 * width) :=
  gidneyAccumulate_interface width

/-- The exact total two-word action preserves an arbitrary external encoded reference jointly. -/
lemma gidneyUnitMultiplication_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (layout := QubitLayout.canonical ((encoding width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width (program width modulus coefficient))
      environment
      (fun state => (unitMultiplicationPairEquiv modulus coefficient state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (gidneyUnitMultiplication_realizes width modulus coefficient)

end

end QuantumAlg.MAU.Multiplication.Gidney
