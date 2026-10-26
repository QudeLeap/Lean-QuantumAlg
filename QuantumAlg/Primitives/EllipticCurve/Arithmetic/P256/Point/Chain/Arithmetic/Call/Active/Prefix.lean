/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Multiplication
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl

/-! # Concrete active actual prefixes, including the real saved-product program -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma window_word_eq_of_reads (port : WordPort) (first second : Window.Raw)
    (reads : ∀ index, (Window.pointBit (port.bit index)).get first =
      (Window.pointBit (port.bit index)).get second) :
    port.value first.1 = port.value second.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  exact (WordPort.bit_get port index first.1).symm.trans
    ((reads index).trans (WordPort.bit_get port index second.1))

private lemma window_word_control_ne (port : WordPort) (index : Fin 256) :
    Window.Enable.outputBit.wire ≠ (Window.pointBit (port.bit index)).wire ∧
      Window.normalBit.wire ≠ (Window.pointBit (port.bit index)).wire := by
  constructor
  · intro same
    have position := congrArg Fin.val same
    rw [Window.Enable.outputBit_wire, Window.pointBit_wire] at position
    exact Native.BorrowedControl.word_ne port index position.symm
  · intro same
    have position := congrArg Fin.val same
    rw [Window.normalBit_wire, Window.pointBit_wire] at position
    have within := Placement.word_before_suffix port index
    omega

private lemma restore_word (port : WordPort) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw) :
    port.value (Control.restoreStep stream width bounded state).1 = port.value state.1 :=
  window_word_eq_of_reads port _ state (fun index =>
    Control.restore_other stream width bounded _ (window_word_control_ne port index).1
      (window_word_control_ne port index).2 state)

private lemma enable_word (port : WordPort) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw) :
    port.value (Window.Enable.step stream width bounded state).1 = port.value state.1 :=
  window_word_eq_of_reads port _ state (fun index =>
    Window.Enable.step_other stream width bounded _ (window_word_control_ne port index).1 state)

attribute [local irreducible] modulus Native.ket Window.ket Inversion.result

lemma division_afterForward_work1 (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.work1 (activeDivisionAfterForward stream width widthBound input positive bounded
      numerator flags address).1 = Horner.zeroWord :=
  (restore_word .work1 stream width widthBound
    (clearedResult input positive bounded numerator flags address)).trans
      (Inversion.result_work1_zero input coprime positive bounded numerator (0, (0, false)) flags)

lemma division_afterForward_work2 (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.work2 (activeDivisionAfterForward stream width widthBound input positive bounded
      numerator flags address).1 = inverseWord input positive bounded :=
  (restore_word .work2 stream width widthBound
    (clearedResult input positive bounded numerator flags address)).trans
      (Inversion.result_value input positive bounded numerator (0, (0, false)) flags)

private lemma initial_work1_zero (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) :
    Frame.work1 (Inversion.initial input numerator (0, (0, false)) flags) = Horner.zeroWord := by
  change Frame.work1 (Inversion.Transport.state Inversion.modulus_size
    (ControlledResident.initial modulus input numerator (0, (0, false)) flags)) = _
  rw [Inversion.transport_work1]
  have zero : ControlledResident.work1
      (ControlledResident.initial modulus input numerator (0, (0, false)) flags) = 0 :=
    initial_largeWord_zero modulus input numerator (0, (0, false)) flags
  rw [zero]
  apply Fin.ext
  change (0 : Fin (2 ^ modulus.size)).val = 0
  exact Fin.val_zero _

/-- The actual division prefix executes its first resident and then saves the real quotient. -/
lemma divisionBeforeReset_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address) :
    (beforeReset .division stream width widthBound).applyNormalized environment
        (Window.ket (activeDivisionInitial stream width widthBound input numerator flags address)) =
      Window.ket (afterSave .enable
        (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address)) := by
  have saved := save_apply .enable environment
    (activeDivisionAfterForward stream width widthBound input positive bounded numerator
      flags address)
    (division_afterForward_work1 stream width widthBound input coprime positive bounded
      numerator flags address)
    (activeDivisionAfterForward_flags stream width widthBound input positive bounded
      numerator flags address) (fun _ => by
        change Canonical (Frame.work2 _)
        rw [division_afterForward_work2]
        exact inverseWord_canonical input coprime positive bounded)
  exact UnitaryCircuit.applyNormalized_seq_of_eq
    (firstResident_active stream width widthBound environment input numerator coprime positive
      bounded flags selected address) saved

/-- The second actual prefix saves the original denominator product before any inverse-X call. -/
lemma multiplicationBeforeReset_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (bounded : input.val < modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    (beforeReset .multiplication stream width widthBound).applyNormalized environment
        (Window.ket (activeMultiplicationInitial stream width widthBound input numerator
          flags address)) =
      Window.ket (afterSave .normal
        (activeMultiplicationInitial stream width widthBound input numerator flags address)) := by
  have zero : Frame.work1 (activeMultiplicationInitial stream width widthBound input numerator
      flags address).1 = Horner.zeroWord :=
    (enable_word .work1 stream width widthBound
      (clearedInitial input numerator flags address)).trans
        (initial_work1_zero input numerator flags)
  have source : Frame.work2 (activeMultiplicationInitial stream width widthBound input numerator
      flags address).1 = Fin.cast
        (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input :=
    (enable_word .work2 stream width widthBound
      (clearedInitial input numerator flags address)).trans
        (Inversion.initial_value input numerator (0, (0, false)) flags)
  exact save_apply .normal environment _ zero
    (activeMultiplicationInitial_flags stream width widthBound input numerator flags address)
    (fun _ => by
      change Canonical (Frame.work2 _)
      rw [source]
      exact bounded)

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
