/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Original
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.State.Update
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Original whole-window output of the real controlled square subtraction

The actual suffix program retains every original address and changes only
the numerical X word. The paid copy/uncompute restores its original zero
A word. The original real flag coordinates and actual active-sector
canonicality are the only arithmetic premises of this lifted endpoint.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

/-- The same actual native square subtraction has this exact original whole-window output. -/
lemma subtractSquareProgram_original_label (environment : OracleModel.empty.Interpretation)
    (state : Raw)
    (flags : ((Placement.layout Native.squarePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Native.squarePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Native.squarePorts).grouping state.1).1.2.2 = false)
    (zero : Frame.work1 state.1 = Horner.zeroWord)
    (sourceAdmitted : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = true →
        Canonical (Frame.numerator state.1))
    (targetAdmitted : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = true →
        Canonical (Frame.work2 state.1)) :
    (suffixProgram Native.BorrowedControl.subtractSquareProgram).applyNormalized environment
        (ket state) =
      ket (resultSetConstant (resultWord .work2)
        (Accumulate.Inverse.differenceWord (Frame.numerator state.1) (Frame.numerator state.1)
          (Frame.work2 state.1) ((Native.BorrowedControl.controlBit Native.squarePorts).get
            ((Placement.layout Native.squarePorts).grouping state.1).2.2)) state) := by
  let value := Accumulate.Inverse.differenceWord (Frame.numerator state.1)
    (Frame.numerator state.1) (Frame.work2 state.1)
      ((Native.BorrowedControl.controlBit Native.squarePorts).get
        ((Placement.layout Native.squarePorts).grouping state.1).2.2)
  have actual := Native.BorrowedControl.subtractSquareProgram_original environment state.1
    flags zero sourceAdmitted targetAdmitted
  have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    Frame.encoding addressEncoding Native.BorrowedControl.subtractSquareProgram state.1
    (resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value state.1)
    state.2 actual
  change (suffixProgram Native.BorrowedControl.subtractSquareProgram).applyNormalized environment
    (ket state) = ket
      (resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value state.1,
        state.2) at lifted
  have same := EncodedBit.Word.resultSetConstant_onProductLeft addressEncoding
    (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value state.1 state.2
  change resultSetConstant (resultWord .work2) value state = _ at same
  exact lifted.trans (congrArg ket same.symm)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
