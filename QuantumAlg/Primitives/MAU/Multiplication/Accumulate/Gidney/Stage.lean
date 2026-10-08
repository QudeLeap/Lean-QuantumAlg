/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stage.Placement

/-!
# A selected modular offset placed on the original two words

The actual controlled pivot-flip offset borrows two source coordinates
different from its selector and returns them exactly. Its explicit basis
and physical placements share the source-selector wire permutation and
the helper block rotation. No gate is introduced by this placement, and
the target update covers every label with the established identity extension.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open Nat.FixedWidth EncodedBit GateSpec

theorem gidneySelectedWords_output (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (state : CanonicalRegisters extra) :
    selectedWordsEquiv extra selected (canonicalOutput modulus constant state) =
      selectedOutput selected modulus constant (selectedWordsEquiv extra selected state) := by
  unfold selectedOutput
  rw [gidneySelectedWords_selector]
  rcases state with ⟨control, unused, flag, target, helper⟩
  cases control <;> rfl

/-- Relocate each literal instruction by the same certified helper and selector wire map. -/
def placedStageGates (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    List (GateSpec (encoding (extra + 3))) :=
  (canonicalGates extra modulus constant).map (stageFullPlacement extra selected).placeGate

/-- Every source field is restored by the literal stage on the original two-word carrier. -/
theorem gidneyPlacedStageGates_step (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (state : Registers (extra + 3)) :
    stepList (placedStageGates extra selected modulus constant) state =
      selectedOutput selected modulus constant state := by
  rw [placedStageGates, FullPlacement.placeGates_step, FullPlacement.step,
    gidneyCanonicalGates_step]
  change selectedWordsEquiv extra selected
    (canonicalOutput modulus constant ((selectedWordsEquiv extra selected).symm state)) = _
  exact (gidneySelectedWords_output extra selected modulus constant
    ((selectedWordsEquiv extra selected).symm state)).trans
      (congrArg (selectedOutput selected modulus constant)
        ((selectedWordsEquiv extra selected).apply_symm_apply state))

/-- Actual native instructions on the complete original source/target layout. -/
def placedStageProgram (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding (extra + 3)).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (placedStageGates extra selected modulus constant)

/-- Exact coherent semantics, with both arbitrarily initialized borrowed bits returned. -/
theorem gidneyPlacedStage_realizes (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    UnitaryCircuit.Realizes (encoding (extra + 3))
      (placedStageProgram extra selected modulus constant)
      (selectedOutput selected modulus constant) :=
  realizesList_congrStep _ _ _ (gidneyPlacedStageGates_step extra selected modulus constant)

/-- The placement retains each native event in its original execution order. -/
theorem gidneyPlacedStageGates_events (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    (placedStageGates extra selected modulus constant).map (event .empty) =
      (canonicalGates extra modulus constant).map (event .empty) := by
  simp only [placedStageGates, List.map_map, Function.comp_def, FullPlacement.placeGate_event]

/-- Exact wire placement preserves the original native pool and every evaluated duration. -/
theorem gidneyPlacedStage_resources (extra : Nat) (selected : Fin (extra + 3))
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1))
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (placedStageProgram extra selected modulus constant).eventCost =
        (canonicalProgram extra modulus constant).eventCost ∧
      (placedStageProgram extra selected modulus constant).evaluatedEventDepth assign =
        (canonicalProgram extra modulus constant).evaluatedEventDepth assign := by
  constructor
  · simp only [placedStageProgram, canonicalProgram, programList_eventCost,
      gidneyPlacedStageGates_events]
  · simp only [placedStageProgram, canonicalProgram, UnitaryCircuit.evaluatedEventDepth,
      programList_eventDepth, gidneyPlacedStageGates_events]

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
