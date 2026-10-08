/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Latch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights.Probability

/-!
# Original chronological source selection in the actual finite complete loop

The real loop includes every sampled recovery, persistent selection and
physical reset. Its terminal latch integrates the original ordered source
law from the incoming actual latch, with every reference matrix coordinate.
This supplies the finite observation proof justifying interleaved recovery.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Original finite source expectation from the given mathematical initial latch value. -/
def latchedWeight {N : Nat} (input : Input N) (count : Nat)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (initial : CShape.Value (.option (.unsignedWord (modulusBits N)))) : ℂ :=
  SourceWeights.batch input count (fun outcomes => weight
    (NativeFactorScan.firstPresent initial
      (NativeFactorScan.sourceResults input (List.ofFn outcomes))))

private theorem latchedWeight_zero {N : Nat} (input : Input N)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (initial : CShape.Value (.option (.unsignedWord (modulusBits N)))) :
    latchedWeight input 0 weight initial = weight initial := by
  simp only [latchedWeight, SourceWeights.batch, List.ofFn_zero,
    NativeFactorScan.sourceResults, NativeFactorScan.firstPresent_none_right]

private theorem latchedWeight_succ {N : Nat} (input : Input N) (count : Nat)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (initial : CShape.Value (.option (.unsignedWord (modulusBits N)))) :
    latchedWeight input (count + 1) weight initial =
      SourceWeights.one input (fun outcome => latchedWeight input count weight
        (NativeFactorScan.firstPresent initial (NativeFactorScan.sourceResult input outcome))) := by
  unfold latchedWeight
  change SourceWeights.one input (fun first => SourceWeights.batch input count
    (fun rest => weight (NativeFactorScan.firstPresent initial
      (NativeFactorScan.sourceResults input (List.ofFn (Fin.cons first rest)))))) = _
  apply congrArg (SourceWeights.one input)
  funext first
  apply congrArg (SourceWeights.batch input count)
  funext rest
  rw [List.ofFn_cons, NativeFactorScan.sourceResults, NativeFactorScan.firstPresent_assoc]

/-- Every arbitrary-count actual complete loop has the original chronological latch law. -/
theorem Finite.body_latch_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Finite.body ctx N input sameWires cells result count).execute Reference state)
      (fun entry _ => weight (NativeFactorScan.latchValue (Finite.cells ctx N count cells) entry.1))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => latchedWeight input count weight (NativeFactorScan.latchValue cells entry.1))
      left right := by
  induction count generalizing ctx History weight with
  | zero =>
      change ExecutionState.referenceFiberSum
        ((Circuit.id (model := executionModel input) ctx).execute Reference state)
        (fun entry _ => weight (NativeFactorScan.latchValue cells entry.1)) left right =
        ExecutionState.referenceFiberSum state
          (fun entry _ => latchedWeight input 0 weight (NativeFactorScan.latchValue cells entry.1))
          left right
      rw [Circuit.execute_id, ExecutionState.referenceFiberSum_mapClassical]
      simp only [latchedWeight_zero]
  | succ count induction =>
      let first := Completion.code ctx N input sameWires cells result
      let later := Finite.body (Iteration.context ctx N) N input
        ((Iteration.quantumWires ctx N).trans sameWires)
        (Completion.cells ctx N cells) (Completion.liftWrite ctx N result) count
      let finalCells := Finite.cells (Iteration.context ctx N) N count
        (Completion.cells ctx N cells)
      let continuation := latchedWeight input count weight
      have tail := induction (Iteration.context ctx N)
        ((Iteration.quantumWires ctx N).trans sameWires)
        (Completion.cells ctx N cells) (Completion.liftWrite ctx N result)
        (Completion.separated ctx N cells result separated) (first.execute Reference state)
        (Completion.code_seeded ctx N input sameWires cells result state)
        ((first.execute_mass Reference state).trans normalized) weight
      have step := completion_latch_reference ctx N input sameWires cells result separated
        state seeded normalized continuation left right
      have sequence := Circuit.referenceFiberSum_execute_seq first later state
        (fun store => weight (NativeFactorScan.latchValue finalCells store)) left right
      refine sequence.trans (tail.trans (step.trans ?_))
      apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
      funext entry basis
      exact (latchedWeight_succ input count weight
        (NativeFactorScan.latchValue cells entry.1)).symm

/-- The one actual terminal pack exposes precisely the persistent latch value in its real cell. -/
theorem Finite.pack_output_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (count : Nat) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Finite.context ctx N count) Reference
      ((executionModel input).HiddenState × History))
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Finite.pack ctx N input count cells result).execute Reference state)
      (fun entry _ => weight (entry.1.read
        (.storage (Finite.liftWrite ctx N count result).toCStorageRef))) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (NativeFactorScan.latchValue (Finite.cells ctx N count cells) entry.1))
      left right := by
  rw [Finite.pack, BitWord.bitWord_instruction_execute,
    ExecutionState.referenceFiberSum_mapClassical]
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (NativeFactorScan.pack_result (Finite.cells ctx N count cells)
    (Finite.liftWrite ctx N count result) entry.1)

/-- Actual arbitrary-count complete repetition and its paid pack have the original latch law. -/
theorem Finite.code_output_reference (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (count : Nat)
    (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state)
    (normalized : state.IsNormalized)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Finite.code ctx N input sameWires count cells result).execute Reference state)
      (fun entry _ => weight (entry.1.read
        (.storage (Finite.liftWrite ctx N count result).toCStorageRef))) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => latchedWeight input count weight (NativeFactorScan.latchValue cells entry.1))
      left right := by
  let repeated := Finite.body ctx N input sameWires cells result count
  let packed := Finite.pack ctx N input count cells result
  have sequence := Circuit.referenceFiberSum_execute_seq repeated packed state
    (fun store => weight (store.read
      (.storage (Finite.liftWrite ctx N count result).toCStorageRef))) left right
  have actualPack := Finite.pack_output_reference ctx N input count cells result
    (repeated.execute Reference state) weight left right
  exact sequence.trans (actualPack.trans (Finite.body_latch_reference ctx N input sameWires count
    cells result separated state seeded normalized weight left right))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
