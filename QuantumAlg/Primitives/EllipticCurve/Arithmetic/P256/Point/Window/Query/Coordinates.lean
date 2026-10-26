/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Body
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Original numerical operands and controls of each native point query

The actual enable and static stream placement preserve every numerical
word. Its retained control is exactly the paid whole-digit predicate,
while the independent normal bit keeps its original value. Thus final
point consumers need numerical canonicality only on the original active
sectors, rather than an extra coordinate-decomposition premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

attribute [local implicit_reducible] capacity width

lemma arithmeticSource_word (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (port : WordPort) (state : Raw) :
    port.value (arithmeticSource stream width bounded state) = port.value state.1 := by
  rw [arithmeticSource, sourceState_word]
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have actual := enable_result_get stream width bounded port index state
  change (pointBit (port.bit index)).get (Enable.step stream width bounded state) =
    (pointBit (port.bit index)).get state at actual
  simpa only [pointBit_get, WordPort.bit_get] using actual

lemma arithmeticSource_control (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) :
    (Native.BorrowedControl.controlBit ports).get
        ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2 =
      Enable.outputBit.get (Enable.step stream width bounded state) := by
  rw [Native.BorrowedControl.controlBit_get]
  have scan (input : Raw) : Native.BorrowedControl.flag.get (sourceState stream input) =
      Native.BorrowedControl.flag.get input.1 := by
    unfold sourceState
    rw [streamPlacement_grouping]
    split <;> rfl
  have sameBit : pointBit Native.BorrowedControl.flag = Enable.outputBit := by
    apply EncodedBit.eq_of_wire_eq
    apply Fin.ext
    rw [pointBit_wire, Native.BorrowedControl.flag_wire, Enable.outputBit_wire]
  rw [arithmeticSource, scan]
  change (pointBit Native.BorrowedControl.flag).get (Enable.step stream width bounded state) = _
  rw [sameBit]

/-- The original initialized pool supplies the actual complete-digit arithmetic enable. -/
lemma arithmeticSource_selected (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    (Native.BorrowedControl.controlBit ports).get
        ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2 =
      !decide (∀ index, (Enable.digitBit stream width bounded index).get state = false) := by
  rw [arithmeticSource_control]
  exact Enable.step_output_of_zero stream width bounded state (Enable.outputBit_clean state clean)

lemma arithmeticSource_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) :
    (Native.controlBit ports .normal).get
        ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2 =
      normalBit.get state := by
  change (Placement.savedNormal ports).get
    ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2 = _
  rw [Placement.savedNormal_get]
  change Frame.normalBit.get (arithmeticSource stream width bounded state) = _
  have normal (input : Raw) : Frame.normalBit.get (sourceState stream input) =
      normalBit.get input := by
    unfold sourceState
    rw [streamPlacement_grouping]
    split <;> rfl
  rw [arithmeticSource, normal]
  apply Enable.step_other
  intro same
  have positions := congrArg Fin.val same
  rw [Enable.outputBit_wire, normalBit_wire] at positions
  omega

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
