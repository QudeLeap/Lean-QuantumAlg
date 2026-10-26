/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Equivalence

/-!
# Actual coefficient traversal returns the complete original arithmetic result

The original quantum address chooses a positive admitted window in the
same fixed native traversal. Its output is the original full coefficient
arithmetic action, with the entire original metadata and shared pool.
Address preparation, source guarding and their cleanup are subsequent
actual instructions and are not supplied by this result alone.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Exact actual low/signed arithmetic on the original full frame, with no omitted pool bits. -/
lemma program_apply_original_window (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (program width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          (CoefficientWindowProgram.step
            (CoefficientCoordinates.window width (state.2.1.toNat + 1) (by omega))
            (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow) state.1,
              state.2) else state))) := by
  have actual := program_apply_window width positive signed environment state clean zero within
  simpa only [CoefficientCoordinates.windowStep_eq_original] using actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow
