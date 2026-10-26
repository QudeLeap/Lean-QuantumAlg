/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl.Admitted
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State.Update

/-!
# Actual square subtraction on the complete original initialized label

The existing Y-to-A copy, inverse MAC and uncopy change exactly numerical
X. Only the three actual arithmetic flags and the existing A copy word
are clean; the original borrowed F and the full other pool fields remain
explicit. Canonicality is required only when that real F enables arithmetic.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

namespace BorrowedControl

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width
attribute [local irreducible] subtractSquareProgram ket

/-- The real square program replaces only X and restores the original clean A and flags. -/
lemma subtractSquareProgram_original (environment : OracleModel.empty.Interpretation)
    (state : Frame.Raw)
    (flags : ((Placement.layout squarePorts).grouping state).1.1.2 = false ∧
      ((Placement.layout squarePorts).grouping state).1.2.1 = false ∧
        ((Placement.layout squarePorts).grouping state).1.2.2 = false)
    (zero : Frame.work1 state = Horner.zeroWord)
    (sourceAdmitted : (controlBit squarePorts).get
      ((Placement.layout squarePorts).grouping state).2.2 = true →
        Canonical (Frame.numerator state))
    (targetAdmitted : (controlBit squarePorts).get
      ((Placement.layout squarePorts).grouping state).2.2 = true →
        Canonical (Frame.work2 state)) :
    subtractSquareProgram.applyNormalized environment (ket state) =
      ket (resultSetConstant
        (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256)
        (Accumulate.Inverse.differenceWord (Frame.numerator state) (Frame.numerator state)
          (Frame.work2 state) ((controlBit squarePorts).get
            ((Placement.layout squarePorts).grouping state).2.2)) state) := by
  let retained := ((Placement.layout squarePorts).grouping state).2.2
  let value := Accumulate.Inverse.differenceWord (Frame.numerator state) (Frame.numerator state)
    (Frame.work2 state) ((controlBit squarePorts).get retained)
  have represented := state_eq_arithmeticState_of_flags squarePorts state flags
  change state = arithmeticState squarePorts (Frame.numerator state) (Frame.work2 state)
    (Frame.work1 state) retained at represented
  rw [zero] at represented
  have actual := subtractSquareProgram_admitted environment (Frame.numerator state)
    (Frame.work2 state) retained sourceAdmitted targetAdmitted
  have updated := arithmeticState_target_set squarePorts (Frame.numerator state)
    (Frame.work2 state) value Horner.zeroWord retained
  have output : arithmeticState squarePorts (Frame.numerator state) value Horner.zeroWord retained =
      resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value state :=
    updated.trans (congrArg
      (resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value)
      represented.symm)
  exact (congrArg (fun original : Frame.Raw =>
    subtractSquareProgram.applyNormalized environment (ket original)) represented).trans
      (actual.trans (congrArg ket output))

end

end BorrowedControl

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
