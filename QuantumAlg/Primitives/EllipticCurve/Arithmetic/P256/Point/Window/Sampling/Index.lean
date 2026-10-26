/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Window.Chronology

/-! # Logical window rows and the actual chronological index schedule -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

/-- Logical rows stay separate from their high-to-low execution positions. -/
structure WindowIndex where
  stream : Fin 2
  logical : Fin 17

namespace WindowIndex

def full (index : WindowIndex) : Prop := index.logical.val < 16

instance (index : WindowIndex) : Decidable index.full :=
  inferInstanceAs (Decidable (index.logical.val < 16))

def lowerWidth (index : WindowIndex) : Nat := if index.full then 15 else 3

def highRemaining (index : WindowIndex) : Nat := if index.full then 7 else 1

def lowWidth (index : WindowIndex) : Nat := if index.full then 8 else 2

def start (index : WindowIndex) : Nat :=
  if index.full then 4 + 16 * (15 - index.logical.val) else 0

def row (index : WindowIndex) : Fin 34 :=
  if index.stream.val = 0 then index.logical.castAdd 17 else index.logical.natAdd 17

lemma lowerWidth_bound (index : WindowIndex) : index.lowerWidth ≤ 15 := by
  unfold lowerWidth
  split <;> decide

lemma addressWidth (index : WindowIndex) :
    index.highRemaining + index.lowWidth = index.lowerWidth := by
  unfold highRemaining lowWidth lowerWidth
  split <;> rfl

lemma addressBound (index : WindowIndex) : index.highRemaining + index.lowWidth ≤ 15 :=
  index.addressWidth.le.trans index.lowerWidth_bound

lemma lowBound (index : WindowIndex) : index.lowWidth ≤ 8 := by
  unfold lowWidth
  split <;> decide

lemma lowCapacity (index : WindowIndex) : 2 ^ index.lowWidth ≤ 256 := by
  unfold lowWidth
  split <;> decide

lemma within (index : WindowIndex) : index.start + (index.lowerWidth + 1) ≤ 260 := by
  by_cases full : index.full
  · simp only [start, lowerWidth, if_pos full]
    have bound : index.logical.val < 16 := full
    omega
  · simp only [start, lowerWidth, if_neg full]
    decide

end WindowIndex

/-- Generator stream precedes target-inverse stream; each starts at its high four-bit tail. -/
def chronologicalIndex (position : Fin 34) : WindowIndex :=
  match (finSumFinEquiv : Fin 17 ⊕ Fin 17 ≃ Fin (17 + 17)).symm position with
  | .inl index => WindowIndex.mk (Fin.mk 0 (by decide)) index.rev
  | .inr index => WindowIndex.mk (Fin.mk 1 (by decide)) index.rev

lemma chronologicalIndex_first (position : Fin 17) :
    chronologicalIndex (position.castAdd 17) = ⟨0, position.rev⟩ := by
  simp only [chronologicalIndex, finSumFinEquiv_symm_apply_castAdd]
  rfl

lemma chronologicalIndex_second (position : Fin 17) :
    chronologicalIndex (position.natAdd 17) = ⟨1, position.rev⟩ := by
  simp only [chronologicalIndex, finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The physical driver requests the exact row used by the new chronological seed family. -/
lemma chronologicalIndex_row (position : Fin 34) :
    (chronologicalIndex position).row = Nat.FixedWidth.Window.Chronology.paired 17 position := by
  refine Fin.addCases (m := 17) (n := 17) (fun index => ?_) (fun index => ?_) position
  · rw [chronologicalIndex_first, Nat.FixedWidth.Window.Chronology.paired_first]
    rfl
  · rw [chronologicalIndex_second, Nat.FixedWidth.Window.Chronology.paired_second]
    rfl

/-- A compact symbolic list, with no circuit gate list unfolded at width256 or260. -/
def schedule : List WindowIndex := (List.finRange 34).map chronologicalIndex

lemma schedule_length : schedule.length = 34 := by
  simp only [schedule, List.length_map, List.length_finRange]

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
