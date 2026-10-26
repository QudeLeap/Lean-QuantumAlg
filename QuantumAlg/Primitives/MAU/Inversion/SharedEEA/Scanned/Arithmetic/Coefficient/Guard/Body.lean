/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Guard.Predicate
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Prepared.Inverse

/-!
# Actual coefficient source arithmetic with paid complete address cleanup

The public source-instruction choice selects forward signed addition or
the actual low-subtraction adjoint. Both are fixed native programs, use
the original quantum metadata, and restore the entire shared pool.
The source-phase guard is supplied by a separate actual program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientGuard

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The original coefficient instruction selects a fixed actual native arithmetic program. -/
def bodyProgram (width : Nat) (positive : 1 ≤ width) (signed : Bool) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  if signed then CoefficientAddress.program width positive true
  else CoefficientAddress.inverseProgram width positive false

/-- Disabled original Ctrl retains every complete finite address and original register. -/
lemma bodyProgram_apply_disabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (bodyProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  cases signed with
  | false =>
      exact CoefficientAddress.inverseProgram_apply_disabled
        width positive false environment state clean zero disabled
  | true =>
      exact CoefficientAddress.program_apply_disabled
        width positive true environment state clean zero disabled

/-- Both source modes have their exact full original action and complete native cleanup. -/
lemma bodyProgram_apply_enabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.control = true) (accepted : CoefficientAddress.admitted width state.1) :
    (bodyProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (CoefficientWindowProgram.step
            (CoefficientCoordinates.window width (CoefficientAddress.wordLength width state.1)
              (CoefficientAddress.wordLength_fits width state.1 accepted))
            (operation signed) state.1, state.2))) := by
  cases signed with
  | false =>
      exact CoefficientAddress.inverseProgram_apply_enabled
        width positive false environment state clean zero addressZero enabled accepted
  | true =>
      exact CoefficientAddress.program_apply_enabled
        width positive true environment state clean zero addressZero enabled accepted

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientGuard
