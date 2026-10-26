/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Equivalence
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Body.Inactive
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Body.Inactive

/-! # The actual unchanged low or signed native addition body for aligned remainder work words -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderWindow

noncomputable section

open EncodedBit

/-- This public source-instruction choice changes no quantum-dependent program construction. -/
def program (width : Nat) : Bool → UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum
  | false => ArithmeticWindow.program width
  | true => ArithmeticSignedWindow.program width

/-- Independent low or signed addition on the template's literal low-word source positions. -/
def step (width length : Nat) (fits : length ≤ width + 3) : Bool → Data width → Data width
  | false => (ArithmeticWindow.placement width length fits).step
  | true => ArithmeticTop.windowStep width length fits

private lemma length_congr (width left right : Nat)
    (leftFits : left ≤ width + 3) (rightFits : right ≤ width + 3) (signed : Bool)
    (same : left = right) :
    step width left leftFits signed = step width right rightFits signed := by
  subst right
  rfl

/-- The fixed actual body has the exact runtime-address action with the complete original pool. -/
lemma program_apply (width : Nat) (positive : 1 ≤ width) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(NumberTheory.SharedEEA.ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (within : state.2.1.toNat < width + 3) :
    (program width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (if state.1.control then
          step width (state.2.1.toNat + 1) (by omega) signed state else state))) := by
  cases signed with
  | false =>
      exact ArithmeticWindow.program_apply_window width positive environment state clean zero within
  | true =>
      exact ArithmeticSignedWindow.program_apply_window width positive environment state
        clean zero within

/-- Disabled complete native bodies retain every finite address and all arbitrary source fields. -/
lemma program_apply_disabled (width : Nat) (signed : Bool)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (clean : state.2.2.1 = 0#(NumberTheory.SharedEEA.ScanMetadata.addressWidth width))
    (zero : state.2.2.2 = false) (disabled : state.1.control = false) :
    (program width signed).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state)) := by
  cases signed with
  | false =>
      exact ArithmeticWindow.program_apply_disabled width environment state clean zero disabled
  | true =>
      exact ArithmeticSignedWindow.program_apply_disabled width environment state
        clean zero disabled

/-- Both native actions return the complete alignment of the corresponding original output. -/
lemma step_aligned {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (signed : Bool) (state : Data width) :
    step width window.length (RemainderCoordinates.fits window) signed
        ((ArithmeticAlignment.Fixed.frame width window.below).grouping state) =
      (ArithmeticAlignment.Fixed.frame width window.below).grouping
        (ArithmeticWindowProgram.step window (if signed then .addSigned else .addLow) state.1,
          state.2) := by
  cases signed with
  | false => exact RemainderCoordinates.aligned_low window state
  | true => exact RemainderCoordinates.aligned_signed window state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderWindow
