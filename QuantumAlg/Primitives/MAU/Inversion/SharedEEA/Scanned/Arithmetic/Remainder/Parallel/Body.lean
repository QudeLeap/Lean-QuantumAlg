/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Parallel.Inverse

/-! # Direct signed-subtraction and low-addback action of the actual paired remainder body -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Disabled arithmetic restores all finite source values and the full arbitrary address. -/
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
  | false => exact program_apply_disabled width positive false environment state clean zero disabled
  | true =>
      exact inverseProgram_apply_disabled width positive true environment state clean zero disabled

/-- The same actual source body implements the independent original full-window arithmetic. -/
lemma bodyProgram_apply_enabled (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (enabled : state.1.control = true) (accepted : admitted width state.1) :
    (bodyProgram width positive signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (ArithmeticWindowProgram.step (window width state.1 accepted)
            (if signed then .subtractSigned else .addLow) state.1, state.2))) := by
  cases signed with
  | false =>
      exact program_apply_enabled width positive false environment state clean zero addressZero
        enabled accepted
  | true =>
      exact inverseProgram_apply_enabled width positive true environment state clean zero
        addressZero enabled accepted

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderAddress.Parallel
