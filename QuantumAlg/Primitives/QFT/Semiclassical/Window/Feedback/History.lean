/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Scalars
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Store

/-!
# Exact causal factors read from the retained Fourier history

The actual native feedback word reads every declared result position, but
only earlier positions in its own stream select a phase. Structural list
products reduce that same word to the finite product of its real stored
reads, without changing circuit syntax or assuming any future outcome.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

private lemma atPhase_product (ports : Ports ctx totalBits active) (current : Fin active)
    (stored : Store ctx) (previous : List (BitPosition totalBits)) :
    atPhase ports current stored previous =
      (previous.map (fun position => onePhase ports position current stored)).prod := by
  induction previous with
  | nil => rfl
  | cons previous rest ih =>
      rw [atPhase, ih, List.map_cons, List.prod_cons]
      exact mul_comm _ _

private lemma priorPhases_double_product (ports : Ports ctx totalBits active)
    (stored : Store ctx) (current : Fin active) :
    priorPhases ports stored current =
      ∏ stream : Fin 2, ∏ previous : Fin totalBits,
        onePhase ports (stream, previous) current stored := by
  rw [priorPhases, atPhase_product]
  unfold previousPositions
  rw [List.map_flatMap, List.flatMap_def, List.prod_flatten, List.map_map,
    ← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro stream _
  change ((List.finRange totalBits).map (fun position => (stream, position)) |>.map
    (fun position => onePhase ports position current stored) |>.prod) = _
  rw [List.map_map, ← Fin.prod_univ_def]
  rfl

/-- Exact global offsets and the same original stored bits determine each native phase. -/
lemma window_priorPhases_history (ports : Ports ctx totalBits active) (stored : Store ctx)
    (current : Fin active) :
    priorPhases ports stored current =
      ∏ previous : Fin totalBits,
        if previous.val < ports.start ∧
            (stored.read (.storage
              (ports.results (ports.stream, previous)).toCStorageRef)).toFin.val = 1 then
          Partner.rotation true ((ports.position current).val - previous.val - 1)
        else 1 := by
  rw [priorPhases_double_product]
  refine (Finset.prod_eq_single ports.stream ?_ ?_).trans ?_
  · intro stream _ different
    apply Finset.prod_eq_one
    intro previous _
    have excluded : ¬ ports.past (stream, previous) := fun same => different same.1
    simp only [onePhase, if_neg excluded]
  · simp
  · apply Finset.prod_congr rfl
    intro previous _
    by_cases past : previous.val < ports.start <;>
      by_cases one :
        (stored.read (.storage
          (ports.results (ports.stream, previous)).toCStorageRef)).toFin.val = 1 <;>
      simp only [onePhase, Ports.past, true_and, false_and, past, one, ↓reduceIte]

/-- A stream's first real window has no inherited phase, regardless of all initial cell values. -/
lemma window_priorPhases_start_zero (ports : Ports ctx totalBits active) (stored : Store ctx)
    (first : ports.start = 0) (current : Fin active) :
    priorPhases ports stored current = 1 := by
  rw [window_priorPhases_history]
  apply Finset.prod_eq_one
  intro previous _
  simp only [first, Nat.not_lt_zero, false_and, ↓reduceIte]

/-- Only previously recorded same-stream cells matter; every other original cell is arbitrary. -/
lemma window_priorPhases_store_congr (ports : Ports ctx totalBits active)
    (first second : Store ctx)
    (same : ∀ previous, ports.past previous →
      first.read (.storage (ports.results previous).toCStorageRef) =
        second.read (.storage (ports.results previous).toCStorageRef)) :
    priorPhases ports first = priorPhases ports second := by
  funext current
  rw [window_priorPhases_history, window_priorPhases_history]
  apply Finset.prod_congr rfl
  intro previous _
  by_cases past : previous.val < ports.start
  · rw [same (ports.stream, previous) ⟨rfl, past⟩]
  · simp only [past, false_and, ↓reduceIte]

/-- Actual current-window writes preserve every inherited phase already recorded at its entry. -/
lemma window_priorPhases_outcomeStore (ports : Ports ctx totalBits active)
    (stored : Store ctx) (outcome : Bits active) :
    priorPhases ports (outcomeStore active ports stored outcome) = priorPhases ports stored := by
  apply window_priorPhases_store_congr
  intro previous past
  exact window_outcomeStore_past_read ports stored outcome previous past

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
