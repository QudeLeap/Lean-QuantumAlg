/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Parallel
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Trace

/-!
# Exact subtraction from the actual parallel TTK word

This word is purely unitary. Each inverse is an actual native instruction on
the original wires; the existing adjoint construction retains disjoint parallel
branches and reverses the real source dependencies. The subtraction semantics
and borrowed operand remain those of [HRS16, paper.tex:217-225].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

/-- Execute the actual native adjoint of the rescheduled unitary TTK adder. -/
def parallelSubtractionProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  (parallelLowRippleProgram n).dagger (AlgorithmGate.oracleFreeAdjoints .empty)

/-- Reversing the actual native word preserves the source subtraction event ledger. -/
lemma ttkParallelSubtraction_eventTrace (n : Nat) :
    (parallelSubtractionProgram n).eventTrace = (subtractionProgram n).eventTrace := by
  rw [parallelSubtractionProgram, AlgorithmGate.oracleFreeAdjoints_eventTrace,
    ttkParallelLowRipple_eventTrace]
  simp only [lowRippleProgram, subtractionProgram, subtractionGates,
    programList_eventTrace, List.map_reverse]

/-- Native coordinate counts are identical to the source inverse list. -/
lemma ttkParallelSubtraction_eventCost (n : Nat) :
    (parallelSubtractionProgram n).eventCost = (subtractionProgram n).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, ttkParallelSubtraction_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Actual native inversion retains the dependency depth of the forward schedule. -/
lemma ttkParallelSubtraction_unitDepth (n : Nat) :
    (parallelSubtractionProgram n).evaluatedEventDepth (fun _ => 1) =
      (parallelLowRippleProgram n).evaluatedEventDepth (fun _ => 1) :=
  AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth .empty (parallelLowRippleProgram n)

/-- The actual inverse circuit restores the subtrahend on every encoded input. -/
lemma ttkParallelSubtraction_realizes (n : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding n) (parallelSubtractionProgram n) environment
      subtractionOutput := by
  apply UnitaryCircuit.Realizes.dagger_of_rightInverse
    (ttkParallelLowRipple_realizes_fold n environment)
  · rw [parallelSubtractionProgram, UnitaryCircuit.dagger_matrix]
    have same : (AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment =
        environment := Subsingleton.elim _ _
    rw [same]
    exact Unitary.star_eq_inv _
  · intro input
    rw [← ttkSubtraction_step n input]
    change stepList (lowRippleGates n) (stepList ((lowRippleGates n).reverse) input) = input
    simpa only [List.reverse_reverse] using
      stepList_reverse_stepList ((lowRippleGates n).reverse) input

end

end QuantumAlg.MAU.Addition.TTK
