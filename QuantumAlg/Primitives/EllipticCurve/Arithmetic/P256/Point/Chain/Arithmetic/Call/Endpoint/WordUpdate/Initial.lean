/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint

/-!
# Complete initialized labels under original word changes

The original initializer depends on its input only through Work2. All
three Work1 tail bits, every finite metadata field and the entire pool
are retained explicitly. These are mathematical label identities; the
actual paid quantum seed remains an enclosing execution obligation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private def eraseInput {width : Nat} (state : ControlledResidentFrame.Data width) :
    ControlledResidentFrame.Data width :=
  ((({ state.1.1.1 with secondWord := 0 }, state.1.1.2), state.1.2), state.2)

private def setNumeratorAt {width : Nat} (state : ControlledResidentFrame.Data width)
    (value : Fin (2 ^ width)) : ControlledResidentFrame.Data width :=
  ((state.1.1, value), state.2)

private lemma eraseInput_initial (modulus : Nat)
    (first second numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    eraseInput (ControlledResident.initial modulus first numerator pool flags) =
      eraseInput (ControlledResident.initial modulus second numerator pool flags) := rfl

private lemma setNumeratorAt_initial (modulus : Nat)
    (input first second : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    setNumeratorAt (ControlledResident.initial modulus input first pool flags) second =
      ControlledResident.initial modulus input second pool flags := rfl

/-- Erase only the whole original Work2, retaining all other complete label fields. -/
private def fixedPart (state : Window.Raw) : Window.Raw :=
  (eraseInput (width := 256) state.1, state.2)

private lemma fixedPart_transport {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) (address : Window.Address) :
    fixedPart (Inversion.Transport.state same state, address) =
      (Inversion.Transport.state same (eraseInput state), address) := by
  cases same
  rfl

private lemma withNumerator_transport {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) (value : Fin (2 ^ width))
    (address : Window.Address) :
    withNumerator (Inversion.Transport.state same state, address)
        (Fin.cast (congrArg (fun size => 2 ^ size) same) value) =
      (Inversion.Transport.state same (setNumeratorAt state value), address) := by
  cases same
  rfl

attribute [local irreducible] modulus

private lemma clearedInitial_fixedPart
    (first second numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    fixedPart (clearedInitial first numerator flags address) =
      fixedPart (clearedInitial second numerator flags address) := by
  have source := eraseInput_initial modulus first second numerator (0, (0, false)) flags
  exact (fixedPart_transport Inversion.modulus_size _ address).trans
    ((congrArg (fun state : ControlledResidentFrame.Data modulus.size =>
      (Inversion.Transport.state Inversion.modulus_size state, address)) source).trans
        (fixedPart_transport Inversion.modulus_size _ address).symm)

/-- Replacing Y preserves the full paid initializer, including every fixed auxiliary field. -/
lemma clearedInitial_withNumerator
    (input first second : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    withNumerator (clearedInitial input first flags address)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second) =
      clearedInitial input second flags address := by
  have source := setNumeratorAt_initial modulus input first second (0, (0, false)) flags
  exact (withNumerator_transport Inversion.modulus_size _ second address).trans
    (congrArg (fun state : ControlledResidentFrame.Data modulus.size =>
      (Inversion.Transport.state Inversion.modulus_size state, address)) source)

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
