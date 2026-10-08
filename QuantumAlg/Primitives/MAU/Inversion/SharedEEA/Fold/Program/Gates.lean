/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Gates.Trace

/-! # Complete literal comparison, flag and reflection word for input folding -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldProgram

noncomputable section

open EncodedBit GateSpec Addition.Gidney FoldSourceProgram

private def sourceGates (modulus : Nat) :
    List (GateSpec (Addition.Gidney.encoding (wordWidth modulus))) :=
  comparisonGates (wordWidth modulus) (comparisonPivot modulus) ++
    [.x (flagBit (wordWidth modulus))] ++ biFlipGates (wordWidth modulus) (reflectionPivot modulus)

private theorem sourceGates_step (modulus : Nat)
    (state : Addition.Gidney.Registers (wordWidth modulus)) :
    stepList (sourceGates modulus) state = FoldSourceProgram.step modulus state := by
  rw [sourceGates, stepList_append, stepList_append, gidneyComparisonGates_step,
    gidneyBiFlipGates_step]
  exact component_steps modulus state

private theorem sourceGates_trace (modulus : Nat) :
    (sourceGates modulus).map (event .empty) = (FoldSourceProgram.program modulus).eventTrace := by
  simp only [sourceGates, List.map_append, gidneyComparisonGates_trace,
    FoldSourceProgram.program, UnitaryCircuit.seq_eventTrace, biFlipProgram, programList_eventTrace]
  rfl

/-- The original fold's actual native instructions at every original source-register address. -/
def gates (modulus : Nat) : List (GateSpec (encoding modulus.size)) :=
  FoldComparisonPlacement.placeGates modulus.size (sourceGates modulus)

/-- All input labels retain every spectator and dirty helper under the exact native fold. -/
theorem foldProgram_gates_step (modulus : Nat) (state : Registers modulus.size) :
    stepList (gates modulus) state = step modulus state := by
  erw [gates, FoldComparisonPlacement.foldComparison_placeGates_step, sourceGates_step]
  rfl

/-- Execute the complete comparison and reflection word on the original frame. -/
def nativeProgram (modulus : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (gates modulus)

/-- The literal emitted word preserves all original amplitudes, phases and arbitrary helpers. -/
theorem foldProgram_nativeProgram_realizes (modulus : Nat) :
    UnitaryCircuit.Realizes (encoding modulus.size) (nativeProgram modulus) (step modulus) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _ (foldProgram_gates_step modulus)

/-- Complete physical placement preserves every actual original fold instruction in order. -/
theorem foldProgram_gates_trace (modulus : Nat) :
    (gates modulus).map (event .empty) = (program modulus).eventTrace := by
  erw [gates, FoldComparisonPlacement.foldComparison_placeGates_trace,
    sourceGates_trace, program_eventTrace]

/-- The actual emitted program retains the original ordered native trace. -/
theorem foldProgram_nativeProgram_trace (modulus : Nat) :
    (nativeProgram modulus).eventTrace = (program modulus).eventTrace := by
  rw [nativeProgram, programList_eventTrace, foldProgram_gates_trace]

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldProgram
