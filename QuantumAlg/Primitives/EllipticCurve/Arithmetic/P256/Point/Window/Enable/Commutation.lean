/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor.Action
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber

/-!
# Actual enable commutes with replacing a numerical word

The whole-digit predicate reads only its original stream and address.
Replacing a separate numerical word preserves that predicate and its
real output, so both actual enable directions commute with this exact
full-label update. The bitwise proof is generic before specialization.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open EncodedBit

lemma toggleStep_flip_comm {Data : Type} {labels : BinaryLabelEncoding Data} {controls : Nat}
    (ports : Word.OneDirtyLayout (encoding := labels) controls) (observed : EncodedBit labels)
    (outside : ∀ index, observed.wire ≠ (ports.source.bit index).wire) (state : Data) :
    toggleStep ports (observed.flip state) = observed.flip (toggleStep ports state) := by
  have read (index) : (ports.source.bit index).get (observed.flip state) =
      (ports.source.bit index).get state :=
    get_flip_of_wire_ne observed _ (outside index) state
  simp only [toggleStep, read]
  split
  · rfl
  · exact flip_comm ports.output observed state

lemma toggleStep_resultSetConstant_comm {Data : Type} {labels : BinaryLabelEncoding Data}
    {controls width : Nat} (ports : Word.OneDirtyLayout (encoding := labels) controls)
    (word : EncodedBit.Word labels width)
    (controlsFree : ∀ bit index, (word.bit bit).wire ≠ (ports.source.bit index).wire)
    (outputFree : ∀ bit, ports.output.wire ≠ (word.bit bit).wire)
    (value : Fin (2 ^ width)) (state : Data) :
    toggleStep ports (WindowLookup.resultSetConstant word value state) =
      WindowLookup.resultSetConstant word value (toggleStep ports state) := by
  have read (index) : (word.bit index).get (toggleStep ports state) =
      (word.bit index).get state := toggleStep_other ports _ (outputFree index) state
  simp only [WindowLookup.resultSetConstant, read]
  exact Word.action_xorConstantStep_comm (toggleStep ports) word _
    (fun bit input => toggleStep_flip_comm ports (word.bit bit) (controlsFree bit) input) state

/-- The actual digit enable and inverse retain every original numerical word setter. -/
lemma step_resultSetConstant_comm (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (port : WordPort) (value : Fin (2 ^ 256)) (state : Raw) :
    step stream width bounded (WindowLookup.resultSetConstant (resultWord port) value state) =
      WindowLookup.resultSetConstant (resultWord port) value (step stream width bounded state) := by
  apply toggleStep_resultSetConstant_comm
  · intro bit index same
    have positions := congrArg Fin.val same
    change ((resultWord port).bit bit).wire.val =
      (digitBit stream width bounded index).wire.val at positions
    rw [resultWord_wire, digitBit_wire] at positions
    have within := bit.isLt
    cases port <;> simp only [WordPort.physicalIndex] at positions <;>
      split_ifs at positions <;> omega
  · intro bit same
    have positions := congrArg Fin.val same
    change outputBit.wire.val = ((resultWord port).bit bit).wire.val at positions
    rw [outputBit_wire, resultWord_wire] at positions
    have within := bit.isLt
    cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
