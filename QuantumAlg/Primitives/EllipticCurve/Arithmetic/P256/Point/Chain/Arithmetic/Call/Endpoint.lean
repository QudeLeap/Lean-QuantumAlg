/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Product
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Inactive.Coherent

/-!
# A common complete initialized label for the actual two measured calls

The label is obtained by the actual whole-digit enable toggle on the
initialized resident source. All source padding and small fields remain
explicit. Arithmetic conditions are needed only when the corresponding
real selector is true; disabled binary words remain unrestricted.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma reference_ket_smul_congr {Physical Reference : Register} {Label : Type}
    (basis : Label → Physical.Index) (scalar : ℂ) (first second : Label) (same : first = second)
    (reference : Reference.Index) :
    scalar • (NormalizedVector.ket (R := Physical.prod Reference) (basis first, reference)).vec =
      scalar • (NormalizedVector.ket (R := Physical.prod Reference)
        (basis second, reference)).vec :=
  congrArg (fun value => scalar •
    (NormalizedVector.ket (R := Physical.prod Reference) (basis value, reference)).vec) same

/-- The original arithmetic domain, imposed only in the selected sector. -/
structure ActiveDomain (input numerator : Fin (2 ^ modulus.size)) : Prop where
  coprime : Nat.Coprime input.val modulus
  positive : 0 < input.val
  bounded : input.val < modulus
  canonical : numerator.val < modulus

/-- The same real paid enable toggle precedes both arithmetic calls. -/
def inputState (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  activeMultiplicationInitial stream width bounded input numerator flags address

lemma inputState_eq (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    inputState stream width bounded input numerator flags address =
      activeMultiplicationInitial stream width bounded input numerator flags address := rfl

/-- Replace only the original physical Y word, keeping the entire original source. -/
def withNumerator (state : Window.Raw) (value : Word) : Window.Raw :=
  (((state.1.1.1, value), state.1.2), state.2)

lemma withNumerator_source (state : Window.Raw) (value : Word) :
    (withNumerator state value).1.1.1 = state.1.1.1 := rfl

lemma withNumerator_flags (state : Window.Raw) (value : Word) :
    (withNumerator state value).1.2 = state.1.2 := rfl

lemma withNumerator_address (state : Window.Raw) (value : Word) :
    (withNumerator state value).2 = state.2 := rfl

lemma withNumerator_numerator (state : Window.Raw) (value : Word) :
    Frame.numerator (withNumerator state value).1 = value := rfl

lemma withNumerator_self (state : Window.Raw) :
    withNumerator state (Frame.numerator state.1) = state := rfl

private lemma transport_control {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) :
    (Inversion.Transport.state same state).1.1.1.control = state.1.1.1.control := by
  cases same
  rfl

private lemma initial_source_control (modulus : Nat)
    (input numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (ControlledResident.initial modulus input numerator pool flags).1.1.1.control = false := rfl

attribute [local irreducible] modulus Inversion.initial

lemma inputState_flags (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    ((Placement.layout Save.ports).grouping
      (inputState stream width bounded input numerator flags address).1).1.1.2 = false ∧
    ((Placement.layout Save.ports).grouping
      (inputState stream width bounded input numerator flags address).1).1.2.1 = false ∧
    ((Placement.layout Save.ports).grouping
      (inputState stream width bounded input numerator flags address).1).1.2.2 = false :=
  activeMultiplicationInitial_flags stream width bounded input numerator flags address

lemma inputState_work1 (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Frame.work1 (inputState stream width bounded input numerator flags address).1 =
      Horner.zeroWord :=
  (enable_word .work1 stream width bounded
    (clearedInitial input numerator flags address)).trans
      (initial_work1_zero input numerator flags)

lemma inputState_work2 (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Frame.work2 (inputState stream width bounded input numerator flags address).1 =
      Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input :=
  (enable_word .work2 stream width bounded (clearedInitial input numerator flags address)).trans
    (Inversion.initial_value input numerator (0, (0, false)) flags)

lemma inputState_numerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Frame.numerator (inputState stream width bounded input numerator flags address).1 =
      Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator :=
  (enable_numerator stream width bounded (clearedInitial input numerator flags address)).trans
    ((congrArg Frame.numerator (initial_physical_label input numerator flags)).trans
      ((Inversion.Transport.state_numerator Inversion.modulus_size _).trans
        (congrArg (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size))
          (ControlledResident.initial_numerator modulus input numerator (0, (0, false)) flags))))

lemma inputState_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.normalBit.get (inputState stream width bounded input numerator flags address) =
      flags.2.1 :=
  multiplication_initial_normal stream width bounded input numerator flags address

lemma inputState_clear (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.Enable.step stream width bounded
      (inputState stream width bounded input numerator flags address) =
        clearedInitial input numerator flags address :=
  Window.Enable.step_step stream width bounded (clearedInitial input numerator flags address)

lemma inputState_clear_clean (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Frame.CleanPool (Window.Enable.step stream width bounded
      (inputState stream width bounded input numerator flags address)).1 :=
  (congrArg (fun state : Window.Raw => state.1.1.1.2)
    (inputState_clear stream width bounded input numerator flags address)).trans
      (initial_clean_pool input numerator flags)

lemma inputState_clear_control (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    (Window.Enable.step stream width bounded
      (inputState stream width bounded input numerator flags address)).1.1.1.1.control = false := by
  rw [inputState_clear]
  exact (congrArg (fun state : Frame.Raw => state.1.1.1.control)
    (initial_physical_label input numerator flags)).trans
      ((transport_control Inversion.modulus_size _).trans
        (initial_source_control modulus input numerator (0, (0, false)) flags))

lemma inputState_clear_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    (Window.Enable.step stream width bounded
      (inputState stream width bounded input numerator flags address)).1.2.2.1 = flags.2.1 := by
  rw [inputState_clear]
  exact (congrArg (fun state : Frame.Raw => state.2.2.1)
    (initial_physical_label input numerator flags)).trans
      ((congrArg (fun controls : Frame.Controls => controls.2.1)
        ((Inversion.Transport.state_flags Inversion.modulus_size _).trans
          (ControlledResident.initial_flags modulus input numerator (0, (0, false)) flags))))

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
