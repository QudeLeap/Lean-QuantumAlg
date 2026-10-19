/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Arithmetic

/-!
# Actual constant comparison with two arbitrary bits

The nonzero branch executes an extended HRS offset, a restoring low-word
HRS offset, and one X on the leading flag. Pivot zero executes identity.
This is the addition/restore comparison construction [G17, paper.tex:380-389],
using the separately proved HRS offsets. Every input and both initial bit
values are covered exactly; the helper is restored, and the flag is xor
toggled rather than assumed to start at zero.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec

/-- Actual HRS low-word offset, leaving the leading flag untouched. -/
def lowOffsetProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.onCanonicalBinarySuffix 1 (HRS.oneDirtyProgram width constant)

lemma gidneyLowOffset_realizes (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes (encoding width) (lowOffsetProgram width constant) environment
      (lowOffsetOutput constant) :=
  (UnitaryCircuit.Realizes.onBinarySuffix (left := BinaryLabelEncoding.bool)
    (HRS.hrsOneDirty_realizes width constant)).congrStep (fun _ => rfl)

/-- One actual X gate on the comparison target. -/
def flagFlipProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  program (.x (flagBit width)) (QubitLayout.canonical (encoding width).width) .empty

lemma gidneyFlagFlip_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (flagFlipProgram width) environment flagFlipOutput :=
  (realizes (QubitLayout.canonical (encoding width).width) .empty
    (.x (flagBit width)) environment).congrStep (fun _ => rfl)

/-- Zero-event declaration of all existing systems, with no additional wire or gate. -/
def identityProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.identity AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum

lemma gidneyIdentity_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (identityProgram width) environment id :=
  UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
    (encoding width) (QubitLayout.canonical (encoding width).width) environment

/-- Three actual arithmetic blocks, before the zero-event complete-layout declaration. -/
def positiveComparisonProgram (width pivot : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  ((packedOffsetProgram width (extendedNegatedPivot width pivot)).seq
    (lowOffsetProgram width (pivotWord width pivot))).seq (flagFlipProgram width)

/-- All fitted pivots, including zero and the full capacity, use the same exact carrier. -/
def comparisonProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  if pivot.val = 0 then identityProgram width
  else positiveComparisonProgram width pivot.val

lemma gidneyPositiveComparison_realizes (width pivot : Nat)
    (hpositive : 0 < pivot) (hpivot : pivot ≤ 2 ^ width) :
    UnitaryCircuit.Realizes (encoding width) (positiveComparisonProgram width pivot) environment
      (comparisonOutput pivot) :=
  (((gidneyPackedOffset_realizes width (extendedNegatedPivot width pivot)).seq
      (gidneyLowOffset_realizes width (pivotWord width pivot))).seq
    (gidneyFlagFlip_realizes width)).congrStep
      (gidneyComparison_positive_steps width pivot hpositive hpivot)

/-- Every joint basis label has exactly the comparison action, without relative phase. -/
lemma gidneyComparison_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (comparisonProgram width pivot) environment
      (comparisonOutput pivot.val) := by
  by_cases hzero : pivot.val = 0
  · rw [comparisonProgram, if_pos hzero]
    exact (gidneyIdentity_realizes width).congrStep fun state => by
      change state = comparisonOutput pivot.val state
      simpa only [hzero] using (gidneyComparison_zero width state).symm
  · rw [comparisonProgram, if_neg hzero]
    exact gidneyPositiveComparison_realizes width pivot.val (by omega)
      (by have := pivot.isLt; omega)

/-- The complete comparison interface is the target word and its two arbitrary bits. -/
lemma gidneyComparison_interface (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (encoding width).width = width + 2 ∧
      (QubitLayout.canonical (encoding width).width).systemIdx =
        List.range (width + 2) := by
  exact gidneyPackedOffset_interface width (extendedNegatedPivot width pivot.val)

/-- The exact endpoint also preserves every joint correlation with an encoded reference. -/
lemma gidneyComparison_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (layout := QubitLayout.canonical ((encoding width).width + reference.width))
      (UnitaryCircuit.onBinaryPrefix reference.width (comparisonProgram width pivot)) environment
      (fun state => (comparisonOutput pivot.val state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (gidneyComparison_realizes width pivot)

end

end QuantumAlg.MAU.Addition.Gidney
