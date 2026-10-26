/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Gates
import all QuantumAlg.Components.Encoded.BitGates.Parallel
import all QuantumAlg.Components.Encoded.BitGates.Realization
import Mathlib.Data.List.OfFn

/-!
# TTK with actual parallel first and final CNOT stages

The two independent CNOT stages use real parallel native nodes. The carry and
operand chains retain their source order and complete data dependencies. This
keeps the source operator, every native gate, and the same two operand words,
and derives low-word depth `5n-5` for widths at least two. The source stages are
given in [TTK09, qic-loglogaddition-quant.tex:285-318]; its resource discussion
includes the separate overflow output [TTK09, qic-loglogaddition-quant.tex:357-372].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

private lemma independent_pairs (n : Nat) (physical : QubitLayout (encoding n).width)
    (i j : Fin n) (different : i ≠ j) :
    Disjoint
      (physicalSupport physical (.cnot (leftBit n i) (rightBit n i)
        (ttkLeftRight_disjoint n i i)))
      (physicalSupport physical (.cnot (leftBit n j) (rightBit n j)
        (ttkLeftRight_disjoint n j j))) := by
  rw [physicalSupport_cnot, physicalSupport_cnot]
  simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨⟨ttkLeftLeft_disjoint n i j different, ttkLeftRight_disjoint n i j⟩,
    ⟨Ne.symm (ttkLeftRight_disjoint n j i), ttkRightRight_disjoint n i j different⟩⟩

/-- Stage one uses disjoint actual operand-pair supports after physical placement. -/
lemma ttk_preXor_independent (n : Nat) (physical : QubitLayout (encoding n).width) :
    (preXorGates n).Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second)) := by
  rw [preXorGates, List.pairwise_ofFn]
  intro i j before
  apply independent_pairs
  intro same
  have equal := congrArg Fin.val same
  have ordered : i.val < j.val := before
  change i.val + 1 = j.val + 1 at equal
  omega

/-- The final source CNOTs have disjoint actual control/target pairs. -/
lemma ttk_finalXor_independent (n : Nat) (physical : QubitLayout (encoding n).width) :
    (finalXorGates n).Pairwise (fun first second =>
      Disjoint (physicalSupport physical first) (physicalSupport physical second)) := by
  rw [finalXorGates, List.pairwise_ofFn]
  intro i j before
  exact independent_pairs n physical i j (ne_of_lt before)

/-- The four dependency-sensitive middle stages remain in their original order. -/
def middleRippleGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  descendingXorGates n ++ carryGates n ++
    descendingUncomputeGates n ++ ascendingXorGates n

/-- Actual low-word addition with parallel independent CNOT stages and no new wires. -/
def parallelLowRippleProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  let physical := QubitLayout.canonical (encoding n).width
  (parallelProgramList physical .empty (preXorGates n) (ttk_preXor_independent n physical)).seq
    ((programList physical .empty (middleRippleGates n)).seq
      (parallelProgramList physical .empty (finalXorGates n)
        (ttk_finalXor_independent n physical)))

/-- The native traversal retains the exact original low-word event sequence. -/
lemma ttkParallelLowRipple_eventTrace (n : Nat) :
    (parallelLowRippleProgram n).eventTrace = (lowRippleProgram n).eventTrace := by
  simp only [parallelLowRippleProgram, UnitaryCircuit.seq_eventTrace,
    parallelProgramList_eventTrace, programList_eventTrace, lowRippleProgram,
    lowRippleGates, middleRippleGates, List.map_append, List.append_assoc]

/-- Every native coordinate has the same count as in the source gate word. -/
lemma ttkParallelLowRipple_eventCost (n : Nat) :
    (parallelLowRippleProgram n).eventCost = (lowRippleProgram n).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    ttkParallelLowRipple_eventTrace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The full ambient operator retains all input amplitudes and relative phases. -/
lemma ttkParallelLowRipple_matrix (n : Nat) (environment : OracleModel.empty.Interpretation) :
    (parallelLowRippleProgram n).matrix environment = (lowRippleProgram n).matrix environment := by
  simp only [parallelLowRippleProgram, UnitaryCircuit.seq_matrix, parallelProgramList_matrix,
    lowRippleProgram, lowRippleGates, middleRippleGates,
    gateSpec_programList_append_matrix, mul_assoc]

/-- The rescheduled circuit implements the same complete encoded gate fold. -/
lemma ttkParallelLowRipple_realizes_fold (n : Nat)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding n) (parallelLowRippleProgram n) environment
      (stepList (lowRippleGates n)) where
  apply_encoded_ket := by
    intro input
    simpa only [UnitaryCircuit.applyNormalized, ttkParallelLowRipple_matrix] using
      (ttkLowRipple_realizes_fold (environment := environment) n).apply_encoded_ket input

private lemma middle_length (n : Nat) :
    (middleRippleGates n).length = 3 * (n - 1) + 2 * (n - 2) := by
  simp [middleRippleGates, descendingXorGates, carryGates, descendingUncomputeGates,
    ascendingXorGates, List.length_flatten, List.sum_ofFn]
  omega

/-- Exact all-width unit depth of the actual schedule, including empty and width-one cases. -/
lemma ttkParallelLowRipple_unitDepth (n : Nat) :
    (parallelLowRippleProgram n).evaluatedEventDepth (fun _ => 1) =
      (if n - 1 = 0 then 0 else 1) + (3 * (n - 1) + 2 * (n - 2)) +
        (if n = 0 then 0 else 1) := by
  rw [parallelLowRippleProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq, parallelProgramList_unitDepth,
    parallelProgramList_unitDepth, programList_evaluatedEventDepth_unit, middle_length]
  simp only [preXorGates, finalXorGates, List.ofFn_eq_nil_iff]
  omega

/-- At applicable widths the same gates and two words now have depth `5n-5`. -/
lemma ttkParallelLowRipple_depth_of_two_le (n : Nat) (width : 2 ≤ n) :
    (parallelLowRippleProgram n).evaluatedEventDepth (fun _ => 1) = 5 * n - 5 := by
  rw [ttkParallelLowRipple_unitDepth]
  have positive : n ≠ 0 := by omega
  have more : n - 1 ≠ 0 := by omega
  rw [if_neg positive, if_neg more]
  omega

/-- The canonical gate/query quantum-time model obeys the actual parallel depth bound. -/
lemma ttkParallelLowRipple_quantumTime_le (n : Nat) (width : 2 ≤ n) :
    (parallelLowRippleProgram n).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ 5 * n - 5 := by
  calc
    _ ≤ (parallelLowRippleProgram n).evaluatedEventDepth (fun _ => 1) :=
      DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one _
    _ = _ := ttkParallelLowRipple_depth_of_two_le n width

/-- The empty operand interface executes no gate. -/
lemma ttkParallelLowRipple_depth_zero :
    (parallelLowRippleProgram 0).evaluatedEventDepth (fun _ => 1) = 0 := by
  rw [ttkParallelLowRipple_unitDepth]
  rfl

/-- Width one consists of its one actual sum CNOT. -/
lemma ttkParallelLowRipple_depth_one :
    (parallelLowRippleProgram 1).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [ttkParallelLowRipple_unitDepth]
  rfl

end

end QuantumAlg.MAU.Addition.TTK
