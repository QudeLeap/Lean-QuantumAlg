/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Native
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources

/-! # Actual native coordinates of complete metadata geometry words -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit

/-- The source TTK CNOT count is retained by both literal native orientations. -/
lemma nativeFieldGates_cnot_count (width : Nat) (positive : 1 ≤ width) (field : Field)
    (subtract : Bool) :
    ((nativeFieldGates width positive field subtract).map GateSpec.cnotMultiplicity).sum =
      fullWidth width + 2 * (fullWidth width - 1) + 2 * (fullWidth width - 2) := by
  have placed := GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty
    (placement width positive field).nativeGates_eventTrace
  have source := Addition.TTK.ttkLowRipple_cnot_count (fullWidth width)
  rw [Addition.TTK.lowRippleProgram, GateSpec.programList_cnot_count_eq_sum] at source
  cases subtract <;>
    simpa only [nativeFieldGates, Bool.false_eq_true, if_false, if_true,
      List.map_reverse, List.sum_reverse] using placed.trans source

/-- Native subtraction is actual gate reversal, with the same precise source Toffoli count. -/
lemma nativeFieldGates_toffoli_count (width : Nat) (positive : 1 ≤ width) (field : Field)
    (subtract : Bool) :
    ((nativeFieldGates width positive field subtract).map GateSpec.toffoliMultiplicity).sum =
      2 * (fullWidth width - 1) := by
  have placed := GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty
    (placement width positive field).nativeGates_eventTrace
  have source := Addition.TTK.ttkLowRipple_toffoli_count (fullWidth width)
  rw [Addition.TTK.lowRippleProgram, GateSpec.programList_toffoli_count_eq_sum] at source
  cases subtract <;>
    simpa only [nativeFieldGates, Bool.false_eq_true, if_false, if_true,
      List.map_reverse, List.sum_reverse] using placed.trans source

/-- Actual constant loading adds no CNOT to the source geometry word. -/
lemma nativeConstantGates_cnot_count (width : Nat) (constant : BitVec (fullWidth width)) :
    ((nativeConstantGates width constant).map GateSpec.cnotMultiplicity).sum = 0 :=
  (littleTarget width).xorConstantGates_cnotMultiplicity_sum constant.toFin

/-- Actual public constant loading adds no Toffoli to the source geometry word. -/
lemma nativeConstantGates_toffoli_count (width : Nat) (constant : BitVec (fullWidth width)) :
    ((nativeConstantGates width constant).map GateSpec.toffoliMultiplicity).sum = 0 :=
  (littleTarget width).xorConstantGates_toffoliMultiplicity_sum constant.toFin

/-- Both fixed source phases charge every complete metadata arithmetic CNOT. -/
lemma nativeCoefficientGates_cnot_count (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    ((nativeCoefficientGates width positive deshift).map GateSpec.cnotMultiplicity).sum =
      (if deshift then 2 else 1) *
        (fullWidth width + 2 * (fullWidth width - 1) + 2 * (fullWidth width - 2)) := by
  cases deshift <;>
    simp only [nativeCoefficientGates, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, nativeConstantGates_cnot_count,
      nativeFieldGates_cnot_count] <;> omega

/-- Every original source Toffoli remains in the two complete finite geometry equations. -/
lemma nativeCoefficientGates_toffoli_count (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    ((nativeCoefficientGates width positive deshift).map GateSpec.toffoliMultiplicity).sum =
      (if deshift then 2 else 1) * (2 * (fullWidth width - 1)) := by
  cases deshift <;>
    simp only [nativeCoefficientGates, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, nativeConstantGates_toffoli_count,
      nativeFieldGates_toffoli_count] <;> omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
