/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.SourceProgram
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Actual output reflection controlled by the retained iteration bit

The source keeps the final coefficient when Iter is one and replaces it
by its negative modulo the original prime when Iter is zero
[LYL+26, sec_EEA/sub_4phase.tex:123-125]. Two literal X gates around the
existing coherently controlled bi-flip select precisely that zero branch.
The bi-flip at pivot `p+1` implements `p-t` on the reached coefficient
interval [G17, paper.tex:276-277].

This focused native program retains the original Iter value and restores
an arbitrary helper on every binary input. The total finite action also
specifies labels outside the coefficient interval. Placement on the
actual little-endian Work2 wires, output copying, and reversal of all
retained forward history are separate actual operations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.OutputCorrectionFocus

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Addition.Gidney FoldSourceProgram

/-- Two real flag X gates select the existing controlled reflection on Iter zero. -/
def program (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (Addition.Gidney.encoding (wordWidth modulus)).width).toQuantum :=
  ((flagFlipProgram (wordWidth modulus)).seq
    (biFlipProgram (wordWidth modulus) (reflectionPivot modulus))).seq
      (flagFlipProgram (wordWidth modulus))

/-- Total finite-word action, preserving both the original parity and the arbitrary helper. -/
def step (modulus : Nat) (state : Addition.Gidney.Registers (wordWidth modulus)) :
    Addition.Gidney.Registers (wordWidth modulus) :=
  (state.1, (if state.1 then state.2.1 else
    Nat.FixedWidth.biFlipWordOutput (reflectionPivot modulus) state.2.1, state.2.2))

private lemma component_steps (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    flagFlipOutput (biFlipOutput (reflectionPivot modulus) (flagFlipOutput state)) =
      step modulus state := by
  rcases state with ⟨iteration, word, helper⟩
  cases iteration <;> rfl

/-- Exact phase-preserving action of the actual three native blocks on every input label. -/
lemma program_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (Addition.Gidney.encoding (wordWidth modulus)) (program modulus)
      environment
      (step modulus) :=
  (((gidneyFlagFlip_realizes (wordWidth modulus)).seq
    (gidneyBiFlip_realizes (wordWidth modulus) (reflectionPivot modulus))).seq
      (gidneyFlagFlip_realizes (wordWidth modulus))).congrStep (component_steps modulus)

/-- The sign history is retained rather than erased by the output correction. -/
lemma step_iteration (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    (step modulus state).1 = state.1 := rfl

/-- Every value and correlation of the borrowed helper is restored by the actual program. -/
lemma step_helper (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    (step modulus state).2.2 = state.2.2 := rfl

/-- The internally reached coefficient interval gives the source's exact natural correction. -/
lemma step_value (modulus : Nat) (iteration helper : Bool)
    (word : Fin (2 ^ wordWidth modulus)) (bounded : word.val ≤ modulus) :
    (step modulus (iteration, (word, helper))).2.1.val =
      if iteration then word.val else modulus - word.val := by
  have below : word.val < (reflectionPivot modulus).val := by
    change word.val < modulus + 1
    omega
  cases iteration with
  | false =>
    change (Nat.FixedWidth.biFlipWordOutput (reflectionPivot modulus) word).val = _
    simp only [Nat.FixedWidth.biFlipWordOutput, Nat.FixedWidth.biFlip, if_pos below]
    change modulus + 1 - (word.val + 1) = modulus - word.val
    omega
  | true => rfl

/-- The original parity and finite reflection make the full register action involutive. -/
lemma step_involutive (modulus : Nat) : Function.Involutive (step modulus) := by
  rintro ⟨iteration, word, helper⟩
  cases iteration with
  | false =>
    change (false, (Nat.FixedWidth.biFlipWordOutput (reflectionPivot modulus)
      (Nat.FixedWidth.biFlipWordOutput (reflectionPivot modulus) word), helper)) = _
    rw [Nat.FixedWidth.gidneyBiFlipWord_involutive]
  | true => rfl

/-- The actual circuit adjoint has the same total label action and restores its helper. -/
lemma inverse_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (Addition.Gidney.encoding (wordWidth modulus))
      ((program modulus).dagger (AlgorithmGate.oracleFreeAdjoints .empty)) environment
      (step modulus) := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse (program_realizes modulus)
  · rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  · exact step_involutive modulus

/-- The actual trace includes both flag operations and the selected controlled arithmetic body. -/
lemma program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace =
      (flagFlipProgram (wordWidth modulus)).eventTrace ++
        (biFlipProgram (wordWidth modulus) (reflectionPivot modulus)).eventTrace ++
          (flagFlipProgram (wordWidth modulus)).eventTrace := by
  simp only [program, UnitaryCircuit.seq_eventTrace]

/-- Exact event cardinality, including both real parity complements. -/
lemma program_event_count (modulus : Nat) :
    (program modulus).eventCost.card =
      (biFlipProgram (wordWidth modulus) (reflectionPivot modulus)).eventCost.card + 2 := by
  simp only [program, UnitaryCircuit.seq_eventCost, Multiset.card_add,
    gidneyFlagFlip_eventCost, ResourcePool.singleton, Multiset.card_replicate]
  omega

/-- The shared actual coherent control serializes the body and the two parity gates. -/
lemma program_unitDepth (modulus : Nat) :
    (program modulus).evaluatedEventDepth (fun _ => 1) =
      (biFlipProgram (wordWidth modulus) (reflectionPivot modulus)).eventCost.card + 2 := by
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq, gidneyFlagFlip_depth,
    gidneyBiFlip_depth_eq_events]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputCorrectionFocus
