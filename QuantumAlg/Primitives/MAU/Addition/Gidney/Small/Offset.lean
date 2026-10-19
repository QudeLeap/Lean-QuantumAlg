/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small

/-!
# Modular offsets on zero, one, and two target qubits

The three-pivot identity [G17, paper.tex:319-334] is realized with the
literal small-width X/CNOT lists. These branches use only their target
word; no borrowed helper is introduced to satisfy the general comparison
implementation. They supply the small-width branches of accumulation.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Small

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

/-- Select the already proved literal small-width pivot circuit. -/
def pivotProgram : (width : Nat) → width ≤ 2 →
    Fin (2 ^ width + 1) →
      UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical width).toQuantum
  | 0, _, pivot => Zero.circuit pivot
  | 1, _, pivot => One.circuit pivot
  | 2, _, pivot => Two.circuit pivot
  | width + 3, impossible, _ => False.elim (by omega)

lemma gidneySmallPivot_realizes (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.finIdentity width)
      (pivotProgram width small pivot) environment (pivotWordOutput pivot) := by
  interval_cases width
  · exact Zero.gidneySmallZero_realizes pivot
  · exact One.gidneySmallOne_realizes pivot
  · exact Two.gidneySmallTwo_realizes pivot

/-- Each selected pivot has at most three actual native events. -/
lemma gidneySmallPivot_event_count_bound (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width small pivot).eventCost.card ≤ 3 := by
  interval_cases width
  · change (Zero.circuit pivot).eventCost.card ≤ 3
    rw [(Zero.gidneySmallZero_interface pivot).1]
    decide
  · change (One.circuit pivot).eventCost.card ≤ 3
    rw [One.gidneySmallOne_eventCost]
    fin_cases pivot <;> decide
  · change (Two.circuit pivot).eventCost.card ≤ 3
    rw [Two.gidneySmallTwo_eventCost]
    fin_cases pivot <;> decide

lemma gidneySmallPivot_depth_eq_events (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) :
    (pivotProgram width small pivot).evaluatedEventDepth (fun _ => 1) =
      (pivotProgram width small pivot).eventCost.card := by
  interval_cases width
  · change (Zero.circuit pivot).evaluatedEventDepth (fun _ => 1) =
      (Zero.circuit pivot).eventCost.card
    rw [(Zero.gidneySmallZero_interface pivot).1,
      (Zero.gidneySmallZero_interface pivot).2]
    rfl
  · change (One.circuit pivot).evaluatedEventDepth (fun _ => 1) =
      (One.circuit pivot).eventCost.card
    rw [One.gidneySmallOne_eventCost, One.gidneySmallOne_depth]
    fin_cases pivot <;> rfl
  · change (Two.circuit pivot).evaluatedEventDepth (fun _ => 1) =
      (Two.circuit pivot).eventCost.card
    rw [Two.gidneySmallTwo_eventCost, Two.gidneySmallTwo_depth]
    fin_cases pivot <;> rfl

/-- Three actual small pivots on the original target carrier. -/
def modularOffsetProgram (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical width).toQuantum :=
  ((pivotProgram width small (offsetFirstPivot modulus constant)).seq
    (pivotProgram width small modulus)).seq
      (pivotProgram width small (offsetLastPivot modulus constant))

/-- All labels satisfy the same modular-offset/identity-extension contract as the general case. -/
lemma gidneySmallModularOffset_realizes (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.finIdentity width)
      (modularOffsetProgram width small modulus constant)
      environment (modularWordOutput modulus constant) :=
  (((gidneySmallPivot_realizes width small (offsetFirstPivot modulus constant)).seq
    (gidneySmallPivot_realizes width small modulus)).seq
      (gidneySmallPivot_realizes width small (offsetLastPivot modulus constant))).congrStep
        (gidneyModularWord_three_pivots modulus constant)

/-- Literal native ledgers are retained; no effective aggregate operation is substituted. -/
lemma gidneySmallModularOffset_eventCost (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width small modulus constant).eventCost =
      (pivotProgram width small (offsetFirstPivot modulus constant)).eventCost +
        (pivotProgram width small modulus).eventCost +
          (pivotProgram width small (offsetLastPivot modulus constant)).eventCost := by
  simp only [modularOffsetProgram, UnitaryCircuit.seq_eventCost]

lemma gidneySmallModularOffset_depth_eq_events (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width small modulus constant).evaluatedEventDepth (fun _ => 1) =
      (modularOffsetProgram width small modulus constant).eventCost.card := by
  rw [gidneySmallModularOffset_eventCost]
  simp only [modularOffsetProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    gidneySmallPivot_depth_eq_events, Multiset.card_add]

/-- A uniform small-branch bound follows from the three literal pivot lists. -/
lemma gidneySmallModularOffset_event_count_bound (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width small modulus constant).eventCost.card ≤ 9 := by
  rw [gidneySmallModularOffset_eventCost]
  simp only [Multiset.card_add]
  have hfirst := gidneySmallPivot_event_count_bound width small
    (offsetFirstPivot modulus constant)
  have hmiddle := gidneySmallPivot_event_count_bound width small modulus
  have hlast := gidneySmallPivot_event_count_bound width small
    (offsetLastPivot modulus constant)
  omega

end

end QuantumAlg.MAU.Addition.Gidney.Small
