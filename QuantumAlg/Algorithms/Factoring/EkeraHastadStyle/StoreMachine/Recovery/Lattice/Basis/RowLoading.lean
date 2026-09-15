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

/-- The actual second source read precedes initialization of the original third coordinate. -/
def firstRowTailInto (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width) :
    Circuit ctx ctx :=
  .seq (.classical (secondOp pair output)) (Word.PowerOfTwo.into 0 output.b13)

/-- Actual second resize and initialized-one store with both chronological paths. -/
def firstRowTailStep (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width)
    (store : Store ctx) : Store ctx × (firstRowTailInto pair output).Path :=
  let loaded := Word.PowerOfTwo.step 0 output.b13 (store.applyOp (secondOp pair output))
  (loaded.1, ((), loaded.2))

/-- Load the actual first basis row from both original decoded samples and a native constant. -/
def loadFirstBasisRowInto (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width) :
    Circuit ctx ctx := .seq (.classical (firstOp pair output)) (firstRowTailInto pair output)

/-- The complete actual native first-row store and chronological operation paths. -/
def firstRowStep (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width)
    (store : Store ctx) : Store ctx × (loadFirstBasisRowInto pair output).Path :=
  let tailStep := firstRowTailStep pair output (store.applyOp (firstOp pair output))
  (tailStep.1, ((), tailStep.2))

/-- Load the prescribed power into the original caller-owned raw word with no initial premise. -/
abbrev loadPowerOfTwoInto (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit ctx ctx := Word.PowerOfTwo.into count output

/-- Actual initialized raw power store and complete native operation path. -/
abbrev powerStep (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :=
  Word.PowerOfTwo.step count output store

/-- The actual second resize and constant initialization retain every incoming state block. -/
theorem firstRowTailInto_execute (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstRowTailInto pair output).execute Reference state = state.mapClassical (fun entry =>
      ((firstRowTailStep pair output entry.1).1,
        (entry.2, (firstRowTailStep pair output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (secondOp pair output))
    (Word.PowerOfTwo.into 0 output.b13) (fun store => (store.applyOp (secondOp pair output), ()))
    (Word.PowerOfTwo.step 0 output.b13) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (secondOp pair output)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (Word.PowerOfTwo.into_execute 0 output.b13)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual first-row loading preserves every original quantum-reference correlation. -/
theorem loadFirstBasisRowInto_execute (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loadFirstBasisRowInto pair output).execute Reference state = state.mapClassical (fun entry =>
      ((firstRowStep pair output entry.1).1, (entry.2, (firstRowStep pair output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (firstOp pair output))
    (firstRowTailInto pair output) (fun store => (store.applyOp (firstOp pair output), ()))
    (firstRowTailStep pair output) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (firstOp pair output) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (firstRowTailInto_execute pair output) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeLoading
