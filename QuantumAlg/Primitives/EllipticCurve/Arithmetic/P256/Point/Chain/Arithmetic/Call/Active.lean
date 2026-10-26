/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.State
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Character
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Normal
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport

/-!
# Concrete active full-state arithmetic labels

The cleared state is the actual accepted resident initializer, including
all three original A tail systems and every small source field. The paid
temporary-control inverse gives the real division input. Its actual forward
returns the corresponding complete resident result, before Save and reset.
No arithmetic body equation is assumed as a callback.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

lemma prepare_restore (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Control.prepareStep stream width bounded (Control.restoreStep stream width bounded state) =
      state := by
  dsimp only [Control.prepareStep, Control.restoreStep, Control.copyStep]
  rw [EncodedBit.cnotStep_cnotStep _ _ Control.flag_normal_ne]
  exact Window.Enable.step_step stream width bounded state

/-- The real cleared resident initializer, with every address system retained. -/
def clearedInitial (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  (Inversion.initial input numerator (0, (0, false)) flags, address)

/-- The real complete resident result on the identical source, pool, controls and address. -/
def clearedResult (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  (Inversion.result input positive bounded numerator (0, (0, false)) flags, address)

/-- The actual control-transfer inverse prepares the full division input label. -/
def activeDivisionInitial (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  Control.restoreStep stream width bounded (clearedInitial input numerator flags address)

/-- Complete label after the actual first forward, immediately before the actual save. -/
def activeDivisionAfterForward (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  Control.restoreStep stream width widthBound
    (clearedResult input positive bounded numerator flags address)

attribute [local irreducible] Native.ket Window.ket Inversion.Normal.program
  Inversion.initial Inversion.result modulus

lemma firstResident_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address) :
    (Control.firstResidentProgram stream width widthBound).applyNormalized environment
      (Window.ket (activeDivisionInitial stream width widthBound input numerator flags address)) =
      Window.ket (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address) := by
  have prepared : Control.prepareStep stream width widthBound
      (activeDivisionInitial stream width widthBound input numerator flags address) =
        clearedInitial input numerator flags address :=
    prepare_restore stream width widthBound (clearedInitial input numerator flags address)
  have bodyAction : Inversion.Normal.program.applyNormalized environment
      (Native.ket (Control.prepareStep stream width widthBound
        (activeDivisionInitial stream width widthBound input numerator flags address)).1) =
        Native.ket (Inversion.result input positive bounded numerator (0, (0, false)) flags) := by
    have inputFrame : (Control.prepareStep stream width widthBound
        (activeDivisionInitial stream width widthBound input numerator flags address)).1 =
        Inversion.initial input numerator (0, (0, false)) flags :=
      congrArg (fun state : Window.Raw => state.1) prepared
    have inputKet := congrArg Native.ket inputFrame
    exact (congrArg (Inversion.Normal.program.applyNormalized environment) inputKet).trans
      (Inversion.Normal.program_initial_active environment input numerator coprime positive
        bounded (0, (0, false)) rfl rfl rfl flags selected)
  have actual := residentWithTemporary_apply stream width widthBound Inversion.Normal.program
    environment (activeDivisionInitial stream width widthBound input numerator flags address)
    (Inversion.result input positive bounded numerator (0, (0, false)) flags) bodyAction
  have addressRetained : (Control.prepareStep stream width widthBound
      (activeDivisionInitial stream width widthBound input numerator flags address)).2 = address :=
    congrArg Prod.snd prepared
  exact actual.trans (congrArg
    (fun extra => Window.ket (Control.restoreStep stream width widthBound
      (Inversion.result input positive bounded numerator (0, (0, false)) flags, extra)))
    addressRetained)

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
