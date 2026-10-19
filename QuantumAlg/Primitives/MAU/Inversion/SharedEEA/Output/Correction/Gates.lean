/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Correction
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Gates

/-! # Complete literal retained-parity correction at the original Work2 orientation -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.OutputCorrection

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit GateSpec Addition.Gidney FoldSourceProgram

private def sourceGates (modulus : Nat) :
    List (GateSpec (Addition.Gidney.encoding (wordWidth modulus))) :=
  [.x (flagBit (wordWidth modulus))] ++
    biFlipGates (wordWidth modulus) (reflectionPivot modulus) ++ [.x (flagBit (wordWidth modulus))]

private lemma sourceGates_step (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    stepList (sourceGates modulus) state = OutputCorrectionFocus.step modulus state := by
  rw [sourceGates, stepList_append, stepList_append, gidneyBiFlipGates_step]
  exact OutputCorrectionFocus.component_steps modulus state

private lemma sourceGates_trace (modulus : Nat) :
    (sourceGates modulus).map (event .empty) =
      (OutputCorrectionFocus.program modulus).eventTrace := by
  simp only [sourceGates, List.map_append, OutputCorrectionFocus.program,
    UnitaryCircuit.seq_eventTrace, biFlipProgram, programList_eventTrace]
  rfl

/-- Both original flag gates and the real reflection at the complete reversed Work2 placement. -/
def gates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  (FoldComparisonPlacement.placeGates modulus.size (sourceGates modulus)).map
    (OutputOrientation.placement modulus.size).placeGate

/-- The literal list corrects the full frame with every original dirty helper restored. -/
lemma outputCorrection_gates_step (modulus : Nat) (state : Registers modulus.size) :
    stepList (gates modulus) state = step modulus state := by
  rw [gates, FullPlacement.placeGates_step]
  unfold FullPlacement.step
  erw [FoldComparisonPlacement.foldComparison_placeGates_step, sourceGates_step]
  simp only [OutputOrientation.placement_grouping_eq]
  rfl

/-- Emit the complete retained-parity correction on the original finite frame. -/
def nativeProgram (modulus : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates modulus)

/-- Exact full-frame amplitudes include arbitrary spectator, parity and helper values. -/
lemma outputCorrection_nativeProgram_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (nativeProgram modulus) environment (step
      modulus) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _ (outputCorrection_gates_step modulus)
    environment

/-- The literal oriented instructions retain every original correction event in order. -/
lemma outputCorrection_gates_trace (modulus : Nat) :
    (gates modulus).map (event .empty) = (program modulus).eventTrace := by
  simp only [gates, List.map_map, Function.comp_def, FullPlacement.placeGate_event]
  erw [FoldComparisonPlacement.foldComparison_placeGates_trace,
    sourceGates_trace, program_eventTrace]

/-- The executed correction word has exactly the original ordered native trace. -/
lemma outputCorrection_nativeProgram_trace (modulus : Nat) :
    (nativeProgram modulus).eventTrace = (program modulus).eventTrace := by
  rw [nativeProgram, programList_eventTrace, outputCorrection_gates_trace]

/-- Existing independent correction resource formulas apply to the same emitted native word. -/
lemma outputCorrection_nativeProgram_eventCost (modulus : Nat) :
    (nativeProgram modulus).eventCost = (program modulus).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ← UnitaryCircuit.ofList_eventTrace_eq_eventCost, outputCorrection_nativeProgram_trace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputCorrection
