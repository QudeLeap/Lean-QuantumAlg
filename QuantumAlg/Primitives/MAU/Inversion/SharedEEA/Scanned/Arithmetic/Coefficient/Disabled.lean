/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Body.Inactive
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Body.Inactive

/-!
# Disabled coefficient arithmetic retains every complete finite address

The same actual low or signed native template is placed on the original
coefficient positions. Its inactive action restores the complete original
frame and shared pool, including addresses outside the positive-window range.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- A disabled actual coefficient template retains every finite address, including width zero. -/
lemma program_apply_disabled (width : Nat) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  let grouped := (CoefficientFrame.placement width).grouping state
  have pool : grouped.2 = state.2 := CoefficientFrame.grouped_pool width state
  have groupedClean : grouped.2.2.1 = 0#(ScanMetadata.addressWidth width) :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans clean
  have groupedZero : grouped.2.2.2 = false :=
    (congrArg (fun value : Pool width => value.2.2) pool).trans zero
  have groupedDisabled : grouped.1.control = false :=
    (CoefficientFrame.grouped_control width state).trans disabled
  have actual : (sourceProgram width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode grouped))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode grouped)) := by
    cases signed with
    | false =>
        exact ArithmeticWindow.program_apply_disabled width environment grouped
          groupedClean groupedZero groupedDisabled
    | true =>
        exact ArithmeticSignedWindow.program_apply_disabled width environment grouped
          groupedClean groupedZero groupedDisabled
  have placed := (CoefficientFrame.placement width).place_ket_of_eq
    (sourceProgram width signed) grouped grouped actual
  simpa only [program, grouped, Equiv.symm_apply_apply] using placed

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow
