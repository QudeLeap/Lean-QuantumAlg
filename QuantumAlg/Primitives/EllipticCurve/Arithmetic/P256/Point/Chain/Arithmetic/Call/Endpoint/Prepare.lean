/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint

/-! # Internal temporary-N coordinates of the actual initialized division input -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

def setNormal (flags : Frame.Controls) (value : Bool) : Frame.Controls :=
  (flags.1, (value, flags.2.2))

private lemma resident_reflag (modulus : Nat) (input numerator : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags newFlags : ControlledResidentFrame.Flags) :
    ControlledResident.initial modulus input numerator pool newFlags =
      ((ControlledResident.initial modulus input numerator pool flags).1, newFlags) := rfl

private lemma transport_reflag {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) (flags : Frame.Controls) :
    Inversion.Transport.state same (state.1, flags) =
      ((Inversion.Transport.state same state).1, flags) := by
  cases same
  rfl

private lemma normal_flip (state : Window.Raw) :
    Window.normalBit.flip state =
      ((state.1.1, setNormal state.1.2 (!state.1.2.2.1)), state.2) := rfl

attribute [local irreducible] modulus Inversion.initial

lemma clearedInitial_flags (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    (clearedInitial input numerator flags address).1.2 = flags :=
  (congrArg (fun state : Frame.Raw => state.2)
    (initial_physical_label input numerator flags)).trans
      ((Inversion.Transport.state_flags Inversion.modulus_size _).trans
        (ControlledResident.initial_flags modulus input numerator (0, (0, false)) flags))

lemma clearedInitial_reflag (input numerator : Fin (2 ^ modulus.size))
    (flags newFlags : Frame.Controls) (address : Window.Address) :
    clearedInitial input numerator newFlags address =
      (((clearedInitial input numerator flags address).1.1, newFlags), address) := by
  apply Prod.ext
  · change Inversion.initial input numerator (0, (0, false)) newFlags = _
    rw [initial_physical_label, resident_reflag modulus input numerator (0, (0, false))
      flags newFlags, transport_reflag]
    exact congrArg (fun state : Frame.Raw => (state.1, newFlags))
      (initial_physical_label input numerator flags).symm
  · rfl

lemma normal_flip_clearedInitial (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    Window.normalBit.flip (clearedInitial input numerator flags address) =
      clearedInitial input numerator (setNormal flags (!flags.2.1)) address := by
  have read : Window.normalBit.flip (clearedInitial input numerator flags address) =
      (((clearedInitial input numerator flags address).1.1,
        setNormal flags (!flags.2.1)), address) := by
    rw [normal_flip, clearedInitial_flags]
    rfl
  exact read.trans (clearedInitial_reflag input numerator flags
    (setNormal flags (!flags.2.1)) address).symm

/-- The complete whole-digit predicate, on the real cleared initialized label. -/
def divisionEnabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Bool :=
  Control.digitEnabled stream width bounded (clearedInitial input numerator flags address)

/-- N is a temporary digit predicate only for this first inversion call. -/
def divisionFlags (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Frame.Controls :=
  setNormal flags (divisionEnabled stream width bounded input numerator flags address)

lemma division_prepared (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address) :
    Control.prepareStep stream width bounded
        (inputState stream width bounded input numerator flags address) =
      clearedInitial input numerator
        (divisionFlags stream width bounded input numerator flags address) address := by
  have actual := Control.prepare_after_enable stream width bounded
    (clearedInitial input numerator flags address) (initial_clean_pool input numerator flags)
  change Control.prepareStep stream width bounded
    (Window.Enable.step stream width bounded (clearedInitial input numerator flags address)) = _
  rw [actual]
  change (if divisionEnabled stream width bounded input numerator flags address then
    Window.normalBit.flip (clearedInitial input numerator flags address) else
      clearedInitial input numerator flags address) = _
  cases selected : divisionEnabled stream width bounded input numerator flags address with
  | false =>
    rw [if_neg Bool.false_ne_true]
    have same : divisionFlags stream width bounded input numerator flags address = flags := by
      dsimp only [divisionFlags]
      rw [selected]
      exact (congrArg (setNormal flags) normalZero).symm.trans (by rfl)
    rw [same]
  | true =>
    rw [if_pos rfl, normal_flip_clearedInitial]
    congr 1
    dsimp only [divisionFlags]
    rw [selected, normalZero]
    rfl

lemma division_input_eq (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address) :
    inputState stream width bounded input numerator flags address =
      activeDivisionInitial stream width bounded input numerator
        (divisionFlags stream width bounded input numerator flags address) address :=
  (restore_prepare stream width bounded _).symm.trans
    (congrArg (Control.restoreStep stream width bounded)
      (division_prepared stream width bounded input numerator flags normalZero address))

lemma digitEnabled_frontier (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second : Window.Raw) (same : frontier first = frontier second) :
    Control.digitEnabled stream width bounded first =
      Control.digitEnabled stream width bounded second := by
  have predicate :
      (∀ index, (Window.Enable.digitBit stream width bounded index).get first = false) ↔
        (∀ index, (Window.Enable.digitBit stream width bounded index).get second = false) :=
    forall_congr' (fun index => by rw [digit_frontier stream width bounded first second same index])
  simp only [Control.digitEnabled, predicate]

private lemma transport_frontier_congr {width : Nat} (same : width = 256)
    (first second : ControlledResidentFrame.Data width)
    (pool : first.1.1.2 = second.1.1.2) (flags : first.2 = second.2)
    (address : Window.Address) :
    frontier (Inversion.Transport.state same first, address) =
      frontier (Inversion.Transport.state same second, address) := by
  cases same
  exact Prod.ext pool (Prod.ext flags rfl)

private lemma clearedInitial_label (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    clearedInitial input numerator flags address =
      (Inversion.Transport.state Inversion.modulus_size
        (ControlledResident.initial modulus input numerator (0, (0, false)) flags), address) :=
  Prod.ext (initial_physical_label input numerator flags) rfl

private lemma clearedResult_label (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    clearedResult input positive bounded numerator flags address =
      (Inversion.Transport.state Inversion.modulus_size
        (ControlledResident.result modulus input positive bounded numerator
          (0, (0, false)) flags), address) := rfl

private lemma clearedInitial_clean (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    (frontier (clearedInitial input numerator flags address)).1 = (0, (0, false)) :=
  initial_clean_pool input numerator flags

attribute [local irreducible] clearedInitial clearedResult Inversion.result

lemma clearedResult_frontier (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    frontier (clearedResult input positive bounded numerator flags address) =
      frontier (clearedInitial input numerator flags address) := by
  have initialLabel := clearedInitial_label input numerator flags address
  have resultLabel := clearedResult_label input positive bounded numerator flags address
  have pool := (ControlledResident.result_pool modulus input positive bounded numerator
    (0, (0, false)) flags).trans
      (ControlledResident.initial_pool modulus input numerator (0, (0, false)) flags).symm
  have controls := (ControlledResident.result_flags modulus input positive bounded numerator
    (0, (0, false)) flags).trans
      (ControlledResident.initial_flags modulus input numerator (0, (0, false)) flags).symm
  exact (congrArg frontier resultLabel).trans
    ((transport_frontier_congr Inversion.modulus_size _ _ pool controls address).trans
      (congrArg frontier initialLabel).symm)

/-- The first real resident restores the same whole-digit F after its complete forward. -/
lemma division_forward_enable (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    (Phase.physicalSelector .enable).get
        (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address).1 =
      divisionEnabled stream width widthBound input numerator flags address :=
  (Control.flag_get _).symm.trans
    ((Control.restore_flag stream width widthBound
      (clearedResult input positive bounded numerator flags address)
      (Window.Enable.outputBit_clean _
        ((congrArg (fun value : Pool 256 × (Frame.Controls × Window.Address) => value.1)
          (clearedResult_frontier input positive bounded numerator flags address)).trans
            (clearedInitial_clean input numerator flags address)))).trans
      (digitEnabled_frontier stream width widthBound _ _
        (clearedResult_frontier input positive bounded numerator flags address)))

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
