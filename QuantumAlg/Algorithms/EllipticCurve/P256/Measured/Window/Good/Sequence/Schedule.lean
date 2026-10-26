/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Index

/-!
# Symbolic suffixes of the actual chronological window schedule

The induction exposes one indexed window at a time and stops after all
thirty-four positions. It uses list indexing without expanding the schedule
into a concrete list or unfolding any circuit.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

/-- The suffix after all actual chronological windows is empty. -/
lemma schedule_drop_final : Sampling.schedule.drop 34 = [] :=
  List.drop_eq_nil_of_le Sampling.schedule_length.le

/-- Each proper suffix starts at its actual chronological window and keeps the same tail. -/
lemma schedule_drop_cons (processed : Nat) (within : processed < 34) :
    Sampling.schedule.drop processed = Sampling.chronologicalIndex ⟨processed, within⟩ ::
      Sampling.schedule.drop (processed + 1) := by
  have valid : processed < Sampling.schedule.length := by
    rw [Sampling.schedule_length]
    exact within
  rw [List.drop_eq_getElem_cons valid]
  have selected : Sampling.schedule[processed]'valid =
      Sampling.chronologicalIndex ⟨processed, within⟩ := by
    simp only [Sampling.schedule, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  rw [selected]

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
