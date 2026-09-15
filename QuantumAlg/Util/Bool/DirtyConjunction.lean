/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.List.Basic

/-!
# Cancellation through a Boolean conjunction chain

Each pair supplies a read-only control and an arbitrary incoming target bit.
Changing the initial seed propagates exactly through the conjunction of the
controls, independently of every incoming target. Two final controlled flips
therefore cancel all dependence on those arbitrary bits.
-/

namespace Bool.DirtyConjunction

/-- The last value produced by sequential xor updates with arbitrary incoming bits. -/
def ripple (seed : Bool) : List (Bool × Bool) → Bool
  | [] => seed
  | (control, incoming) :: rest => ripple (incoming ^^ (control && seed)) rest

/-- The initial xor difference propagates through precisely the read-only controls. -/
theorem ripple_xor_input (pairs : List (Bool × Bool)) (seed difference : Bool) :
    ripple (seed ^^ difference) pairs =
      (ripple seed pairs ^^ (difference && pairs.all Prod.fst)) := by
  induction pairs generalizing seed difference with
  | nil => simp [ripple]
  | cons pair rest inductionHypothesis =>
      obtain ⟨control, incoming⟩ := pair
      have update : (incoming ^^ (control && (seed ^^ difference))) =
          ((incoming ^^ (control && seed)) ^^ (control && difference)) := by
        cases incoming <;> cases control <;> cases seed <;> cases difference <;> rfl
      change ripple (incoming ^^ (control && (seed ^^ difference))) rest = _
      rw [update, inductionHypothesis]
      simp only [ripple, List.all_cons]
      have propagated : ((control && difference) && rest.all Prod.fst) =
          (difference && (control && rest.all Prod.fst)) := by
        cases control <;> cases difference <;> cases rest.all Prod.fst <;> rfl
      rw [propagated]

/-- The two propagated values differ only by the complete control conjunction. -/
theorem ripple_xor_ripple (pairs : List (Bool × Bool)) (seed difference : Bool) :
    (ripple (seed ^^ difference) pairs ^^ ripple seed pairs) =
      (difference && pairs.all Prod.fst) := by
  rw [ripple_xor_input]
  cases ripple seed pairs <;> cases difference && pairs.all Prod.fst <;> rfl

/-- Two controlled flips remove all arbitrary chain values and retain the desired conjunction. -/
theorem paired_target_flips (pairs : List (Bool × Bool))
    (seed difference lastControl target : Bool) :
    ((target ^^ (ripple (seed ^^ difference) pairs && lastControl)) ^^
        (ripple seed pairs && lastControl)) =
      (target ^^ (difference && pairs.all Prod.fst && lastControl)) := by
  rw [ripple_xor_input]
  cases ripple seed pairs <;> cases difference <;> cases pairs.all Prod.fst <;>
    cases lastControl <;> cases target <;> rfl

end Bool.DirtyConjunction
