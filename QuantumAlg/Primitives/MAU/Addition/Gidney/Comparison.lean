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

open EncodedBit.GateSpec

/-- Actual HRS low-word offset, leaving the leading flag untouched. -/
def lowOffsetProgram (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.prodRight (m := 1) (HRS.oneDirtyProgram width constant)

theorem gidneyLowOffset_realizes (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryCircuit.Realizes (encoding width) (lowOffsetProgram width constant)
      (lowOffsetOutput constant) :=
  (HRS.hrsOneDirty_realizes width constant).prodRight

/-- One actual X gate on the comparison target. -/
def flagFlipProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  program (.x (flagBit width))

theorem gidneyFlagFlip_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (flagFlipProgram width) flagFlipOutput :=
  (realizes (.x (flagBit width))).congrStep (fun _ => rfl)

/-- Zero-event declaration of all existing systems, with no additional wire or gate. -/
def identityProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.identity (Qubits (encoding width).width)
    (List.range (width + 2)) List.nodup_range

theorem gidneyIdentity_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (identityProgram width) id :=
  UnitaryCircuit.Realizes.identityAt _ _ _

/-- Three actual arithmetic blocks, before the zero-event complete-layout declaration. -/
def positiveComparisonProgram (width pivot : Nat) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  ((packedOffsetProgram width (extendedNegatedPivot width pivot)).seq
    (lowOffsetProgram width (pivotWord width pivot))).seq (flagFlipProgram width)

/-- All fitted pivots, including zero and the full capacity, use the same exact carrier. -/
def comparisonProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  if pivot.val = 0 then identityProgram width
  else (positiveComparisonProgram width pivot.val).seq (identityProgram width)

theorem gidneyPositiveComparison_realizes (width pivot : Nat)
    (hpositive : 0 < pivot) (hpivot : pivot ≤ 2 ^ width) :
    UnitaryCircuit.Realizes (encoding width) (positiveComparisonProgram width pivot)
      (comparisonOutput pivot) :=
  (((gidneyPackedOffset_realizes width (extendedNegatedPivot width pivot)).seq
      (gidneyLowOffset_realizes width (pivotWord width pivot))).seq
    (gidneyFlagFlip_realizes width)).congrStep
      (gidneyComparison_positive_steps width pivot hpositive hpivot)

/-- Every joint basis label has exactly the comparison action, without relative phase. -/
theorem gidneyComparison_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (comparisonProgram width pivot)
      (comparisonOutput pivot.val) := by
  by_cases hzero : pivot.val = 0
  · rw [comparisonProgram, if_pos hzero]
    exact (gidneyIdentity_realizes width).congrStep fun state => by
      change state = comparisonOutput pivot.val state
      simpa only [hzero] using (gidneyComparison_zero width state).symm
  · rw [comparisonProgram, if_neg hzero]
    exact (gidneyPositiveComparison_realizes width pivot.val (by omega)
      (by have := pivot.isLt; omega)).seq (gidneyIdentity_realizes width)

private theorem lowOffset_range (width : Nat) (constant : Fin (2 ^ width)) :
    (lowOffsetProgram width constant).physical_idx ⊆ List.range (width + 2) := by
  have hsource : (HRS.oneDirtyProgram width constant).physical_idx ⊆
      List.range (width + 1) := by
    rw [HRS.hrsOneDirty_physical]
    exact fun _ h => h
  have h := UnitaryCircuit.prodRight_physical_idx_subset_range
    (m := 1) (HRS.oneDirtyProgram width constant) hsource
  have hwidth : 1 + (HRS.oneDirtyEncoding width).width = width + 2 := by
    change 1 + (width + 1) = width + 2
    omega
  unfold lowOffsetProgram
  simpa only [hwidth] using h

private theorem positiveComparison_range (width pivot : Nat) :
    (positiveComparisonProgram width pivot).physical_idx ⊆ List.range (width + 2) := by
  have hextended : (packedOffsetProgram width (extendedNegatedPivot width pivot)).physical_idx ⊆
      List.range (width + 2) := by
    rw [gidneyPackedOffset_physical]
    exact fun _ h => h
  have hflag : (flagFlipProgram width).physical_idx ⊆ List.range (width + 2) := by
    have h := program_physical_idx_subset_range (.x (flagBit width))
    have hwidth : (encoding width).width = width + 2 := by
      change 1 + (width + 1) = width + 2
      omega
    unfold flagFlipProgram
    simpa only [hwidth] using h
  unfold positiveComparisonProgram
  exact UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ hextended
      (lowOffset_range width (pivotWord width pivot))) hflag

/-- The same circuit declares exactly the target word and its two arbitrary bits. -/
theorem gidneyComparison_physical (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonProgram width pivot).physical_idx = List.range (width + 2) := by
  by_cases hzero : pivot.val = 0
  · rw [comparisonProgram, if_pos hzero]
    rfl
  · rw [comparisonProgram, if_neg hzero]
    change (positiveComparisonProgram width pivot.val).physical_idx.union
      (List.range (width + 2)) = List.range (width + 2)
    exact (positiveComparison_range width pivot.val).union_eq_right

/-- The exact endpoint also preserves every joint correlation with an encoded reference. -/
theorem gidneyComparison_realizes_with_reference {Reference : Type}
    (reference : BinaryLabelEncoding Reference) (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (encoding width) reference)
      (UnitaryCircuit.prodLeft (n := reference.width) (comparisonProgram width pivot))
      (fun state => (comparisonOutput pivot.val state.1, state.2)) :=
  (gidneyComparison_realizes width pivot).prodLeft

end

end QuantumAlg.MAU.Addition.Gidney
