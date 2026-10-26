/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Blocks

/-!
# Global earlier-outcome phases of a symbolic measured prefix

Each factor is the original native signed rotation at its original global
distance. The exact product is the suffix phase family produced by the
existing one-head recurrence. No circuit or full-width control bank is
constructed, and no operator factors are commuted.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Recorded prefix bits contribute their actual global-distance phases to a later position. -/
def historyPhase (inverse : Bool) (count : Nat) (record : Bits count) (later : Nat) : Complex :=
  ∏ previous : Fin count, if tupleCoordinates count record previous = 1 then
    rotation inverse (count + later - previous.val - 1) else 1

private lemma historyPhase_succ (inverse : Bool) (count : Nat) (head : Fin 2)
    (tail : Bits count) (later : Nat) :
    historyPhase inverse (count + 1) (head, tail) later =
      (if head = 1 then rotation inverse (count + later) else 1) *
        historyPhase inverse count tail later := by
  unfold historyPhase
  rw [Fin.prod_univ_succ]
  simp only [tupleCoordinates_head, tupleCoordinates_tail, Fin.val_zero, Nat.sub_zero,
    Fin.val_succ]
  have leading : count + 1 + later - 1 = count + later := by omega
  rw [leading]
  apply congrArg (fun scalar : Complex =>
    (if head = 1 then rotation inverse (count + later) else 1) * scalar)
  apply Finset.prod_congr rfl
  intro previous _
  have distance : count + 1 + later - (previous.val + 1) - 1 =
      count + later - previous.val - 1 := by omega
  rw [distance]

/-- The exact recursive suffix phases equal the original phase times all real earlier bits. -/
lemma qftPartner_suffixPhases_history (inverse : Bool) :
    ∀ (headCount tailCount : Nat) (phases : Fin (tailCount + headCount) → Complex)
      (front : Bits headCount) (later : Fin tailCount),
      suffixPhases inverse headCount tailCount phases front later =
        suffixFamily tailCount headCount phases later *
          historyPhase inverse headCount front later.val := by
  intro headCount
  induction headCount with
  | zero =>
      intro tailCount phases front later
      simp only [suffixPhases, suffixFamily, historyPhase, Fin.prod_univ_zero, mul_one]
      exact congrArg phases (Fin.ext (Nat.add_zero later.val).symm)
  | succ headCount ih =>
      intro tailCount phases front later
      rcases front with ⟨head, front⟩
      change suffixPhases inverse headCount tailCount
          (updatedPhases inverse (tailCount + headCount) phases head) front later = _
      rw [ih, historyPhase_succ]
      change
        (phases ⟨later.val + headCount + 1, by omega⟩ *
          (if head = 1 then rotation inverse (later.val + headCount) else 1)) *
            historyPhase inverse headCount front later.val =
        phases ⟨later.val + (headCount + 1), by omega⟩ *
          ((if head = 1 then rotation inverse (headCount + later.val) else 1) *
            historyPhase inverse headCount front later.val)
      have same : (⟨later.val + headCount + 1, by omega⟩ : Fin (tailCount + (headCount + 1))) =
          ⟨later.val + (headCount + 1), by omega⟩ :=
        Fin.ext (Nat.add_assoc later.val headCount 1)
      rw [same, Nat.add_comm later.val headCount, mul_assoc]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
