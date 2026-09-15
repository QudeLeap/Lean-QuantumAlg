/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Correction.Focus
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Orientation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Placement

/-!
# Actual retained-parity correction on the original complete EEA frame

The existing word/Iter/Ctrl arithmetic is placed among the untouched
source registers and on the reversed physical Work2 coordinates. Its
complete field action therefore corrects the little-endian coefficient
exactly as specified by the retained Iter value
[LYL+26, sec_EEA/sub_4phase.tex:123-125].

Only the coefficient word changes. The arbitrary original Ctrl helper,
all four lengths, both phases, Sign, Iter, and all Work1 bits are retained.
The same actual native circuit provides both the exact amplitudes and its
resource trace; the mathematical output function supplies no new gate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.OutputCorrection

noncomputable section

private def ordinaryStep (modulus : Nat) (state : Registers modulus.size) :
    Registers modulus.size :=
  (FoldRegisters.grouping modulus.size).symm
    (OutputCorrectionFocus.step modulus (FoldRegisters.grouping modulus.size state).1,
      (FoldRegisters.grouping modulus.size state).2)

private def ordinaryProgram (modulus : Nat) :
    UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  FoldComparisonPlacement.placeFocus modulus.size
    (FoldComparisonFocus.place (modulus.size + 3) (OutputCorrectionFocus.program modulus))

private theorem ordinary_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (ordinaryProgram modulus)
      (ordinaryStep modulus) :=
  (FoldComparisonPlacement.placeFocus_realizes modulus.size
    (FoldComparisonFocus.place_realizes (modulus.size + 3)
      (OutputCorrectionFocus.program_realizes modulus))).congrStep (by
        intro state
        simp only [FoldComparisonPlacement.focusStep, FoldComparisonFocus.placeStep,
          Equiv.symm_apply_apply, ordinaryStep]
        exact congrArg
          (fun focused : Addition.Gidney.Registers (modulus.size + 3) =>
            (FoldRegisters.grouping modulus.size).symm
              (focused, (FoldRegisters.grouping modulus.size state).2))
          ((FoldComparisonFocus.fieldEquiv (modulus.size + 3)).symm_apply_apply
            (OutputCorrectionFocus.step modulus (FoldRegisters.grouping modulus.size state).1)))

private theorem ordinary_physical (modulus : Nat) :
    (ordinaryProgram modulus).physical_idx = List.range (encoding modulus.size).width :=
  FoldComparisonPlacement.placeFocus_physical modulus.size _
    (FoldComparisonFocus.place_physical_range (modulus.size + 3) _
      (OutputCorrectionFocus.program_physical_range modulus))

private theorem ordinary_within (modulus : Nat) :
    (ordinaryProgram modulus).physical_idx ⊆ List.range (encoding modulus.size).width := by
  rw [ordinary_physical]
  exact List.Subset.refl _

/-- The complete field action reads and writes Work2 in its actual little-endian orientation. -/
def step (modulus : Nat) (state : Registers modulus.size) : Registers modulus.size :=
  (OutputOrientation.grouping modulus.size).symm
    (ordinaryStep modulus (OutputOrientation.grouping modulus.size state))

/-- Place the real reflection and both flag X gates on the original little-endian coefficient. -/
def program (modulus : Nat) : UnitaryCircuit (Qubits (encoding modulus.size).width) :=
  (OutputOrientation.placement modulus.size).place (ordinaryProgram modulus)
    (ordinary_within modulus)

/-- Complete exact amplitude action with arbitrary original spectator and helper values. -/
theorem program_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (program modulus) (step modulus) :=
  (OutputOrientation.placement modulus.size).place_realizes
    (ordinary_within modulus) (ordinary_realizes modulus)

/-- Read the resulting Work2 coefficient in its physical little-endian orientation. -/
theorem step_word (modulus : Nat) (state : Registers modulus.size) :
    (step modulus state).secondWord.reverse =
      BitVec.ofFin ((OutputCorrectionFocus.step modulus
        (state.flags.iteration,
          (BitVec.equivFin state.secondWord.reverse, state.control))).2.1) := by
  let corrected : BitVec (modulus.size + 3) :=
    BitVec.ofFin ((OutputCorrectionFocus.step modulus
      (state.flags.iteration, (BitVec.equivFin state.secondWord.reverse, state.control))).2.1)
  change corrected.reverse.reverse = corrected
  exact BitVec.reverse_reverse_eq

/-- No complementary part of the forward history changes during the actual correction. -/
theorem step_retained (modulus : Nat) (state : Registers modulus.size) :
    (step modulus state).firstWord = state.firstWord ∧
      (step modulus state).coefficientLength = state.coefficientLength ∧
      (step modulus state).quotientLength = state.quotientLength ∧
      (step modulus state).divisorLength = state.divisorLength ∧
      (step modulus state).shift = state.shift ∧
      (step modulus state).flags = state.flags ∧
      (step modulus state).control = state.control := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reached coefficient values receive exactly the retained-parity natural correction. -/
theorem step_value (modulus : Nat) (state : Registers modulus.size)
    (bounded : state.secondWord.reverse.toNat ≤ modulus) :
    (step modulus state).secondWord.reverse.toNat =
      if state.flags.iteration then state.secondWord.reverse.toNat
        else modulus - state.secondWord.reverse.toNat := by
  rw [step_word]
  exact OutputCorrectionFocus.step_value modulus state.flags.iteration state.control
    (BitVec.equivFin state.secondWord.reverse) bounded

/-- The actual correction retains exactly the original complete frame footprint. -/
theorem program_physical (modulus : Nat) :
    (program modulus).physical_idx = List.range (encoding modulus.size).width :=
  (OutputOrientation.placement modulus.size).place_physical _ (ordinary_within modulus)

/-- Every elementary event survives both actual coordinate placements. -/
theorem program_eventTrace (modulus : Nat) :
    (program modulus).eventTrace = (OutputCorrectionFocus.program modulus).eventTrace :=
  ((OutputOrientation.placement modulus.size).place_eventTrace _ (ordinary_within modulus)).trans
    ((FoldComparisonPlacement.placeFocus_eventTrace modulus.size _).trans
      (FoldComparisonFocus.place_eventTrace (modulus.size + 3) _))

/-- The actual resource pool is the focused native pool, including its two real flag gates. -/
theorem program_eventCost (modulus : Nat) :
    (program modulus).eventCost = (OutputCorrectionFocus.program modulus).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_eventTrace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputCorrection
