/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Frame

/-! # Exact original flag readouts for the actual finite phase patterns -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

/-- All five actual physical flag positions read their corresponding original register fields. -/
lemma flag_get (width : Nat) (index : Fin 5) (state : Data width) :
    (flag width index).get state =
      ![state.1.flags.first, state.1.flags.second, state.1.flags.sign,
        state.1.flags.iteration, state.1.control] index := by
  fin_cases index <;> rfl

/-- The signed-instruction pattern reads Phase1 and omits Sign. -/
lemma flags_matches_one (width : Nat) (expected : Fin 1 → Bool) (state : Data width) :
    (flags width 1 (by decide)).PatternMatches expected state ↔
      state.1.flags.first = expected 0 := by
  constructor
  · intro matched
    exact matched 0
  · intro matched index
    fin_cases index
    exact matched

/-- Low arithmetic reads precisely the actual Phase1, Phase2 and retained Sign values. -/
lemma flags_matches_three (width : Nat) (expected : Fin 3 → Bool) (state : Data width) :
    (flags width 3 (by decide)).PatternMatches expected state ↔
      state.1.flags.first = expected 0 ∧ state.1.flags.second = expected 1 ∧
        state.1.flags.sign = expected 2 := by
  constructor
  · intro matched
    exact ⟨matched 0, matched 1, matched 2⟩
  · rintro ⟨first, second, sign⟩ index
    fin_cases index
    · exact first
    · exact second
    · exact sign

/-- Original Ctrl is the only actual output of every phase pattern. -/
lemma control_flip (width : Nat) (state : Data width) :
    (flag width 4).flip state =
      ({ state.1 with control := !state.1.control }, state.2) := rfl

/-- Original Iter is the only actual work output of the full geometry validity circuit. -/
lemma iteration_flip (width : Nat) (state : Data width) :
    (flag width 3).flip state =
      ({ state.1 with flags := { state.1.flags with iteration := !state.1.flags.iteration } },
        state.2) := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
