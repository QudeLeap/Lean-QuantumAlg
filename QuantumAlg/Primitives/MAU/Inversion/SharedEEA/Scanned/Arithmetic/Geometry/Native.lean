/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Coefficient

/-!
# Literal geometry gate words for additional coherent source controls

These are actual X/CNOT/Toffoli lists on the same complete geometry
frame. Reversal implements the native inverse word. Their full finite
actions coincide with the already specified metadata arithmetic, so
additional controls can be lowered without a host input callback.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit

/-- The actual ordered TTK word on the original finite metadata and full temporary target. -/
def nativeFieldGates (width : Nat) (positive : 1 ≤ width) (field : Field) (subtract : Bool) :
    List (GateSpec (encoding width)) :=
  if subtract then (placement width positive field).nativeGates.reverse
  else (placement width positive field).nativeGates

/-- Both actual native orientations have the same independent full-frame arithmetic action. -/
lemma nativeFieldGates_step (width : Nat) (positive : 1 ≤ width) (field : Field)
    (subtract : Bool) (state : Data width) :
    GateSpec.stepList (nativeFieldGates width positive field subtract) state =
      if subtract then subtractStep width positive field state
      else step width positive field state := by
  cases subtract with
  | false => exact (placement width positive field).nativeGates_step state
  | true =>
      have inverse := GateSpec.stepList_reverse_stepList
        (placement width positive field).nativeGates (subtractStep width positive field state)
      rw [Addition.TTK.WordPlacement.nativeGates_step] at inverse
      change GateSpec.stepList (placement width positive field).nativeGates.reverse
        (step width positive field (subtractStep width positive field state)) = _ at inverse
      rw [step_subtractStep] at inverse
      exact inverse

/-- The constant's complete bit pattern is emitted through actual physical X instructions. -/
def nativeConstantGates (width : Nat) (constant : BitVec (fullWidth width)) :
    List (GateSpec (encoding width)) :=
  (littleTarget width).xorConstantGates constant.toFin

/-- The literal constant word has exactly the existing full-frame constant-load action. -/
lemma nativeConstantGates_step (width : Nat) (constant : BitVec (fullWidth width))
    (state : Data width) :
    GateSpec.stepList (nativeConstantGates width constant) state =
      constantStep width constant state := rfl

/-- Both fixed source phases expose their complete literal native geometry words. -/
def nativeCoefficientGates (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    List (GateSpec (encoding width)) :=
  nativeConstantGates width (coefficientConstant width deshift) ++
    (if deshift then nativeFieldGates width positive .divisor true ++
      nativeFieldGates width positive .shift true
    else nativeFieldGates width positive .coefficient false)

/-- The same actual source order has precisely the full coefficient-preparation action. -/
lemma nativeCoefficientGates_step (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    GateSpec.stepList (nativeCoefficientGates width positive deshift) state =
      coefficientStep width positive deshift state := by
  cases deshift <;>
    simp only [nativeCoefficientGates, Bool.false_eq_true, if_false, if_true,
      GateSpec.stepList_append, nativeConstantGates_step, nativeFieldGates_step,
      coefficientStep]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
