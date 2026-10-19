/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init

/-!
# Exact sequential phase-control XORs of the shared EEA

After each arithmetic microstep, the source first updates `Phase2`, then
uses that updated bit to update `Sign`. If the shift count is zero, it
complements both phase bits; the final pair exchange also complements
`Iter` [LYL+26, sec_EEA/sub_regshare.tex:303-315]. The order of these XORs
is essential. In particular, completed coefficient extraction enters the
fourth phase with `(Phase1, Phase2, Sign) = (1, 1, 1)`.

This owner implements exactly those finite Boolean assignments and their
inverse, with the three actual length predicates supplied explicitly.
They do not alter the lengths. Arithmetic, word exchange, length refresh,
terminal scheduling, and quantum gates are separate refinements. The
transition laws below retain every intermediate sign and parity bit.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PhaseControl

/-- The four actual source control bits affected by the post-arithmetic updates. -/
@[ext]
structure Flags where
  first : Bool
  second : Bool
  sign : Bool
  iteration : Bool
deriving DecidableEq

/-- Execute the source's post-arithmetic flag assignments in their specified order. -/
def update (quotientEmpty divisorActive shiftZero : Bool) (flags : Flags) : Flags :=
  let updatePhase := quotientEmpty && divisorActive
  let second := if updatePhase then flags.second ^^ flags.sign ^^ flags.first else flags.second
  let sign := if updatePhase then flags.sign ^^ second else flags.sign
  ⟨if shiftZero then !flags.first else flags.first,
    if shiftZero then !second else second, sign,
    if quotientEmpty && shiftZero then !flags.iteration else flags.iteration⟩

/-- Reverse the same ordered assignments at the retained, unchanged length predicates. -/
def rewind (quotientEmpty divisorActive shiftZero : Bool) (flags : Flags) : Flags :=
  let first := if shiftZero then !flags.first else flags.first
  let second := if shiftZero then !flags.second else flags.second
  let updatePhase := quotientEmpty && divisorActive
  let sign := if updatePhase then flags.sign ^^ second else flags.sign
  ⟨first, if updatePhase then second ^^ sign ^^ first else second, sign,
    if quotientEmpty && shiftZero then !flags.iteration else flags.iteration⟩

/-- The actual sequential control update retains enough information for its exact inverse. -/
lemma rewind_update (quotientEmpty divisorActive shiftZero : Bool) (flags : Flags) :
    rewind quotientEmpty divisorActive shiftZero
      (update quotientEmpty divisorActive shiftZero flags) = flags := by
  rcases flags with ⟨first, second, sign, iteration⟩
  cases quotientEmpty <;> cases divisorActive <;> cases shiftZero <;>
    cases first <;> cases second <;> cases sign <;> cases iteration <;> decide

/-- The reverse assignments restore arbitrary updated control states in the other direction. -/
lemma update_rewind (quotientEmpty divisorActive shiftZero : Bool) (flags : Flags) :
    update quotientEmpty divisorActive shiftZero
      (rewind quotientEmpty divisorActive shiftZero flags) = flags := by
  rcases flags with ⟨first, second, sign, iteration⟩
  cases quotientEmpty <;> cases divisorActive <;> cases shiftZero <;>
    cases first <;> cases second <;> cases sign <;> cases iteration <;> decide

/-- No sign or phase information is discarded by the actual control assignments. -/
lemma update_injective (quotientEmpty divisorActive shiftZero : Bool) :
    Function.Injective (update quotientEmpty divisorActive shiftZero) := by
  intro left right same
  calc
    left = rewind quotientEmpty divisorActive shiftZero
        (update quotientEmpty divisorActive shiftZero left) :=
      (rewind_update quotientEmpty divisorActive shiftZero left).symm
    _ = rewind quotientEmpty divisorActive shiftZero
        (update quotientEmpty divisorActive shiftZero right) :=
      congrArg (rewind quotientEmpty divisorActive shiftZero) same
    _ = right := rewind_update quotientEmpty divisorActive shiftZero right

/-- The actual alignment comparison selects continued alignment or division and clears its sign. -/
lemma alignment_transition (comparison iteration : Bool) :
    update true true false ⟨false, false, comparison, iteration⟩ =
      ⟨false, comparison, false, iteration⟩ := by
  cases comparison <;> cases iteration <;> decide

/-- A genuine internal division step preserves its phase and cleared arithmetic sign. -/
lemma division_transition (iteration : Bool) :
    update false true false ⟨false, true, false, iteration⟩ =
      ⟨false, true, false, iteration⟩ := by
  cases iteration <;> decide

/-- Zero remaining shift moves completed quotient extraction into coefficient extraction. -/
lemma division_finish (iteration : Bool) :
    update false true true ⟨false, true, false, iteration⟩ =
      ⟨true, false, false, iteration⟩ := by
  cases iteration <;> decide

/-- A genuine internal coefficient step preserves its phase and cleared arithmetic sign. -/
lemma coefficient_transition (iteration : Bool) :
    update false true false ⟨true, false, false, iteration⟩ =
      ⟨true, false, false, iteration⟩ := by
  cases iteration <;> decide

/-- Exhausting the quotient enters phase four with the source's actual sign bit equal to one. -/
lemma coefficient_finish (iteration : Bool) :
    update true true false ⟨true, false, false, iteration⟩ =
      ⟨true, true, true, iteration⟩ := by
  cases iteration <;> decide

/-- Each fourth-phase comparison reaches sign one before this update, which then clears it. -/
lemma deshift_transition (shiftZero iteration : Bool) :
    update true true shiftZero ⟨true, true, true, iteration⟩ =
      ⟨!shiftZero, !shiftZero, false, if shiftZero then !iteration else iteration⟩ := by
  cases shiftZero <;> cases iteration <;> decide

end QuantumAlg.NumberTheory.SharedEEA.PhaseControl
