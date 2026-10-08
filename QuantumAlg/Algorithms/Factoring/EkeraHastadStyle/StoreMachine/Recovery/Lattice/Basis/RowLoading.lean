/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.RowLoading.Layout

/-!
# Actual native loading of the original raw first basis row

Two actual native resizes read the original decoded sample words. Self-XOR
and increment initialize the third coordinate to one without a caller zero
premise. The power loader uses the same actual native constant component.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N width : Nat}

/-- Native first decoded-sample resize into the original first coordinate. -/
def firstOp (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width) :
    ClassicalOp (.unsignedWord (BatchMachine.JWidth N)) (.unsignedWord width) ctx ctx :=
  .wordResize (BatchMachine.JWidth N) width ctx (writeInput pair.first.j) output.b11

/-- Native second decoded-sample resize into the original second coordinate. -/
def secondOp (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width) :
    ClassicalOp (.unsignedWord (BatchMachine.JWidth N)) (.unsignedWord width) ctx ctx :=
  .wordResize (BatchMachine.JWidth N) width ctx (writeInput pair.second.j) output.b12

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual second source read precedes initialization of the original third coordinate. -/
def firstRowTailInto (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (secondOp pair output))
    (Word.PowerOfTwo.into (model := model) 0 output.b13)

/-- Actual second resize and initialized-one store with both chronological paths. -/
def firstRowTailStep (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width)
    (store : Store ctx) : Store ctx × (firstRowTailInto pair output).Path :=
  let resized := BitWord.instructionStep (execution := model) (secondOp pair output) store
  let loaded := Word.PowerOfTwo.step (model := model) 0 output.b13 resized.1
  (loaded.1, (resized.2, loaded.2))

/-- Load the actual first basis row from both original decoded samples and a native constant. -/
def loadFirstBasisRowInto (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (firstOp pair output))
    (firstRowTailInto pair output)

/-- The complete actual native first-row store and chronological operation paths. -/
def firstRowStep (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width)
    (store : Store ctx) : Store ctx × (loadFirstBasisRowInto pair output).Path :=
  let resized := BitWord.instructionStep (execution := model) (firstOp pair output) store
  let tailStep := firstRowTailStep pair output resized.1
  (tailStep.1, (resized.2, tailStep.2))

/-- Load the prescribed power into the original caller-owned raw word with no initial premise. -/
abbrev loadPowerOfTwoInto (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx := Word.PowerOfTwo.into (model := model) count output

/-- Actual initialized raw power store and complete native operation path. -/
abbrev powerStep (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (loadPowerOfTwoInto (model := model) count output).Path :=
  Word.PowerOfTwo.step (model := model) count output store

/-- The actual second resize and constant initialization retain every incoming state block. -/
theorem firstRowTailInto_execute (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstRowTailInto pair output).execute Reference state = state.mapClassical (fun entry =>
      let actual := firstRowTailStep pair output entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (secondOp pair output))
    (Word.PowerOfTwo.into (model := model) 0 output.b13)
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (secondOp pair output) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := Word.PowerOfTwo.step (model := model) 0 output.b13 before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    (fun reference _history _ current => Word.PowerOfTwo.into_execute 0 output.b13
      reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual first-row loading preserves every original quantum-reference correlation. -/
theorem loadFirstBasisRowInto_execute (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadFirstBasisRowInto pair output).execute Reference state = state.mapClassical (fun entry =>
      let actual := firstRowStep pair output entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (firstOp pair output))
    (firstRowTailInto pair output)
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (firstOp pair output) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := firstRowTailStep pair output before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    (fun reference _history _ current => firstRowTailInto_execute pair output reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading
