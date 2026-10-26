/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Guard.Predicate

/-!
# Complete remainder source action and exact original-Ctrl restoration

The independent result uses the entire original natural metadata and
source phase. It retains every physical pool position. Actual guard
and arithmetic execution are separate from these full-state identities.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderGuard

noncomputable section

open EncodedBit

/-- Complete original arithmetic selected by the actual full-length and source-phase predicate. -/
def step (width : Nat) (signed : Bool) (state : Data width) : Data width :=
  if active : ArithmeticGuard.remainderEnabled width signed state = true then
    ArithmeticAddress.liftSource width
      (ArithmeticWindowProgram.step
        (RemainderAddress.window width state.1 (enabled_admitted width signed state active))
        (operation signed)) state
  else state

/-- The declared complete source result retains the whole physical shared pool. -/
lemma step_pool (width : Nat) (signed : Bool) (state : Data width) :
    (step width signed state).2 = state.2 := by
  unfold step
  split <;> rfl

/-- The actual semantic guard leaves the entire input unchanged when its source test fails. -/
lemma toggle_inactive (width : Nat) (signed : Bool) (state : Data width)
    (inactive : ArithmeticGuard.remainderEnabled width signed state ≠ true) :
    ArithmeticGuard.remainderToggleStep width signed state = state :=
  if_neg inactive

/-- A successful actual semantic guard toggles exactly the original existing Ctrl bit. -/
lemma toggle_active (width : Nat) (signed : Bool) (state : Data width)
    (active : ArithmeticGuard.remainderEnabled width signed state = true) :
    ArithmeticGuard.remainderToggleStep width signed state =
      (ArithmeticGuard.flag width 4).flip state :=
  if_pos active

/-- After the corresponding original body, the same complete guard restores original Ctrl. -/
lemma toggle_body_toggle (width : Nat) (signed : Bool)
    (selected : ArithmeticWindowRegisters.Window width) (state : Data width)
    (active : ArithmeticGuard.remainderEnabled width signed state = true) :
    ArithmeticGuard.remainderToggleStep width signed
        (ArithmeticAddress.liftSource width
          (ArithmeticWindowProgram.step selected (operation signed))
          (ArithmeticGuard.remainderToggleStep width signed state)) =
      ArithmeticAddress.liftSource width
        (ArithmeticWindowProgram.step selected (operation signed)) state := by
  let transform := ArithmeticAddress.liftSource width
    (ArithmeticWindowProgram.step selected (operation signed))
  have afterActive : ArithmeticGuard.remainderEnabled width signed
      ((ArithmeticGuard.flag width 4).flip (transform state)) = true :=
    (enabled_control_flip width signed (transform state)).trans
      ((enabled_original width signed selected state).trans active)
  calc
    ArithmeticGuard.remainderToggleStep width signed
        (transform (ArithmeticGuard.remainderToggleStep width signed state)) =
        ArithmeticGuard.remainderToggleStep width signed
          (transform ((ArithmeticGuard.flag width 4).flip state)) :=
      congrArg (fun value => ArithmeticGuard.remainderToggleStep width signed (transform value))
        (toggle_active width signed state active)
    _ = ArithmeticGuard.remainderToggleStep width signed
        ((ArithmeticGuard.flag width 4).flip (transform state)) :=
      congrArg (ArithmeticGuard.remainderToggleStep width signed)
        (original_control_flip width signed selected state)
    _ = (ArithmeticGuard.flag width 4).flip
        ((ArithmeticGuard.flag width 4).flip (transform state)) :=
      toggle_active width signed _ afterActive
    _ = transform state := flip_flip _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderGuard
