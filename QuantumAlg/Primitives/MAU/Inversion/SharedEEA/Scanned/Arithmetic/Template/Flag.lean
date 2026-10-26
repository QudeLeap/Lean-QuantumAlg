/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template
import all QuantumAlg.Util.ThresholdStream

/-!
# The actual conjunction wire as the moving arithmetic flag

Tuple reassociation below describes the unchanged complete label; it is not
a circuit operation. The native source word acts independently of the flag,
and each actual boundary CNOT toggles exactly that original pool position.
This bridge identifies the native callback with the ordered threshold fold.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Every original source, address and prefix field, beside the existing flag. -/
abbrev FlagBase (width : Nat) := Registers width ×
  (BitVec (ScanMetadata.addressWidth width) × BitVec (ScanMetadata.addressWidth width))

/-- Structural tuple reassociation of the same full physical encoded label. -/
def flagEquiv (width : Nat) : Data width ≃ (FlagBase width × Bool) where
  toFun state := ((state.1, (state.2.1, state.2.2.1)), state.2.2.2)
  invFun pair := (pair.1.1, (pair.1.2.1, (pair.1.2.2, pair.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The physical conjunction flip toggles only the final field of this full label. -/
lemma flagEquiv_flip (width : Nat) (state : Data width) :
    flagEquiv width ((conjunctionBit width).flip state) =
      ((flagEquiv width state).1, !(flagEquiv width state).2) := rfl

/-- Original source-word action, retaining all other components of the base label. -/
def baseAction (width : Nat) (stage : Stage) (index : Nat) (base : FlagBase width) :
    FlagBase width :=
  (flagEquiv width (GateSpec.stepList (source width stage index)
    ((flagEquiv width).symm (base, false)))).1

/-- Exact full-label normalization of the original source word for either flag value. -/
lemma source_flagEquiv (width : Nat) (stage : Stage) (index : Nat)
    (base : FlagBase width) (active : Bool) :
    flagEquiv width (GateSpec.stepList (source width stage index)
      ((flagEquiv width).symm (base, active))) =
        (baseAction width stage index base, active) := by
  have clean : (conjunctionBit width).get (GateSpec.stepList (source width stage index)
      ((flagEquiv width).symm (base, false))) = false :=
    GateSpec.stepList_get_of_bitDisjoint _ _ (payload width stage index).activeDisjoint _
  have zero : flagEquiv width (GateSpec.stepList (source width stage index)
      ((flagEquiv width).symm (base, false))) =
        (baseAction width stage index base, false) := by
    apply Prod.ext
    · rfl
    · exact clean
  cases active with
  | false => exact zero
  | true =>
      have flipped : (flagEquiv width).symm (base, true) =
          (conjunctionBit width).flip ((flagEquiv width).symm (base, false)) := rfl
      have commutes := GateSpec.stepList_flip_comm_of_bitDisjoint
        (source width stage index) (conjunctionBit width)
        (payload width stage index).activeDisjoint ((flagEquiv width).symm (base, false))
      rw [flipped, commutes, flagEquiv_flip, zero]
      rfl

/-- The actual controlled native callback performs payload first, then toggles the flag. -/
lemma callback_flagEquiv (width : Nat) (stage : Stage) (index : Nat)
    (selected : Bool) (base : FlagBase width) (active : Bool) :
    flagEquiv width ((payload width stage index).callbackStep selected
      ((flagEquiv width).symm (base, active))) =
      (if active then baseAction width stage index base else base, active ^^ selected) := by
  cases selected <;> cases active
  · rfl
  · exact source_flagEquiv width stage index base true
  · rfl
  · change flagEquiv width ((conjunctionBit width).flip
      (GateSpec.stepList (source width stage index) ((flagEquiv width).symm (base, true)))) = _
    rw [flagEquiv_flip, source_flagEquiv]
    rfl

/-- The original address controls the threshold toggle; the moving flag controls payload. -/
lemma callback_threshold (width : Nat) (stage : Stage) (index : Nat)
    (enabled : Bool) (last : Nat) (state : Data width) :
    flagEquiv width ((payload width stage index).callbackStep
      (enabled && decide (index = last)) state) =
      ThresholdStream.forwardStep (baseAction width stage) enabled last
        (flagEquiv width state) index := by
  obtain ⟨pair, same⟩ := (flagEquiv width).symm.surjective state
  rw [← same, callback_flagEquiv]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
