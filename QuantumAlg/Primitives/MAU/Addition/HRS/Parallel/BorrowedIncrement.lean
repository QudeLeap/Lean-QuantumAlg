/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.BorrowedIncrement
import all QuantumAlg.Primitives.MAU.Addition.HRS.Parallel.Complement
import all QuantumAlg.Primitives.MAU.Addition.TTK.Parallel.Subtraction

/-!
# HRS borrowed increment with actual parallel independent layers

The same two subtractions and two complements restore the arbitrary borrowed
word. Their source order is unchanged. Parallel TTK CNOT stages and parallel
word complements reduce the actual unit depth to `10n-8` for widths at least
two, with every native gate and both operand words retained
[HRS16, paper.tex:219-224].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

/-- Execute the original HRS identity using the actual rescheduled unitary components. -/
def parallelBorrowedIncrementProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (TTK.encoding n).width).toQuantum :=
  (TTK.parallelSubtractionProgram n).seq ((parallelComplementProgram n).seq
    ((TTK.parallelSubtractionProgram n).seq (parallelComplementProgram n)))

/-- Every source native occurrence is retained in the complete actual program. -/
lemma hrsParallelBorrowedIncrement_eventTrace (n : Nat) :
    (parallelBorrowedIncrementProgram n).eventTrace = (borrowedIncrementProgram n).eventTrace := by
  simp only [parallelBorrowedIncrementProgram, UnitaryCircuit.seq_eventTrace,
    TTK.ttkParallelSubtraction_eventTrace, hrsParallelComplement_eventTrace,
    TTK.subtractionProgram, complementProgram, borrowedIncrementProgram,
    borrowedIncrementGates, programList_eventTrace, List.map_append, List.append_assoc]

/-- All native coordinate counts remain exactly those of the HRS source word. -/
lemma hrsParallelBorrowedIncrement_eventCost (n : Nat) :
    (parallelBorrowedIncrementProgram n).eventCost = (borrowedIncrementProgram n).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, hrsParallelBorrowedIncrement_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Arbitrary borrowed words and their full relative phases are restored exactly. -/
lemma hrsParallelBorrowedIncrement_realizes (n : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (TTK.encoding n) (parallelBorrowedIncrementProgram n) environment
      borrowedIncrementOutput := by
  apply ((TTK.ttkParallelSubtraction_realizes n environment).seq
    ((hrsParallelComplement_realizes n environment).seq
      ((TTK.ttkParallelSubtraction_realizes n environment).seq
        (hrsParallelComplement_realizes n environment)))).congrStep
  intro input
  have same := hrsBorrowedIncrement_step n input
  simpa only [borrowedIncrementGates, stepList_append,
    TTK.ttkSubtraction_step, hrsComplement_step] using same

/-- Exact all-width depth retains the separately certified width-zero and width-one cases. -/
lemma hrsParallelBorrowedIncrement_unitDepth (n : Nat) :
    (parallelBorrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
      2 * (TTK.parallelLowRippleProgram n).evaluatedEventDepth (fun _ => 1) +
        2 * (if n = 0 then 0 else 1) := by
  simp only [parallelBorrowedIncrementProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    TTK.ttkParallelSubtraction_unitDepth, hrsParallelComplement_unitDepth]
  omega

/-- The actual parallel schedule has depth `10n-8` without additional qubits or gates. -/
lemma hrsParallelBorrowedIncrement_depth_of_two_le (n : Nat) (width : 2 ≤ n) :
    (parallelBorrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) = 10 * n - 8 := by
  rw [hrsParallelBorrowedIncrement_unitDepth]
  change 2 * (TTK.parallelLowRippleProgram n).evaluatedEventDepth (fun _ => 1) + _ = _
  rw [TTK.ttkParallelLowRipple_depth_of_two_le n width]
  have positive : n ≠ 0 := by omega
  rw [if_neg positive]
  omega

/-- The same certified schedule bounds canonical quantum computation time. -/
lemma hrsParallelBorrowedIncrement_quantumTime_le (n : Nat) (width : 2 ≤ n) :
    (parallelBorrowedIncrementProgram n).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 10 * n - 8 := by
  calc
    _ ≤ (parallelBorrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) :=
      DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one _
    _ = _ := hrsParallelBorrowedIncrement_depth_of_two_le n width

/-- The empty interface performs neither subtraction nor complement gates. -/
lemma hrsParallelBorrowedIncrement_depth_zero :
    (parallelBorrowedIncrementProgram 0).evaluatedEventDepth (fun _ => 1) = 0 := by
  rw [hrsParallelBorrowedIncrement_unitDepth, TTK.ttkParallelLowRipple_depth_zero]
  rfl

/-- Width one uses two sum CNOTs and two one-qubit complements. -/
lemma hrsParallelBorrowedIncrement_depth_one :
    (parallelBorrowedIncrementProgram 1).evaluatedEventDepth (fun _ => 1) = 4 := by
  rw [hrsParallelBorrowedIncrement_unitDepth, TTK.ttkParallelLowRipple_depth_one]
  rfl

end

end QuantumAlg.MAU.Addition.HRS
