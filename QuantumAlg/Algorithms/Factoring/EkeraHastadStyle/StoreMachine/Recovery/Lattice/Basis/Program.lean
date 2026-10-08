/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.Program.Layout

/-!
# Actual native loading of the original three-row source basis

The actual original first row is followed by the two initialized native powers
in the original second- and third-row cells. The four original zero cells stay
untouched, and the same Circuit interpreter retains the complete actual state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis

open Execution
open ClassicalRoutines
open LatticeLoading

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual initialized power loading into the original two nonzero lower-row words. -/
def powerRowsInto (m ell : Nat) (output : RawOutputRefs ctx width) : Circuit model ctx ctx :=
  .seq (loadPowerOfTwoInto (ell + m) output.b21) (loadPowerOfTwoInto (ell + m) output.b32)

/-- The chronological actual lower-row power stores and complete operation paths. -/
def powerRowsStep (m ell : Nat) (output : RawOutputRefs ctx width) (store : Store ctx) :
    Store ctx × (powerRowsInto m ell output).Path :=
  let second := powerStep (ell + m) output.b21 store
  let third := powerStep (ell + m) output.b32 second.1
  (third.1, (second.2, third.2))

/-- Actual loading of the original rows `(j₁, j₂, 1)`, `(Q, 0, 0)` and `(0, Q, 0)`. -/
def loadBasisInto {m ell : Nat} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) : Circuit model ctx ctx :=
  .seq (loadFirstBasisRowInto pair output) (powerRowsInto m ell output)

/-- The complete actual source-basis store and every chronological native path. -/
def basisStep (m ell : Nat) (pair : BatchMachine.PairRefs ctx N) (output : RawOutputRefs ctx width)
    (store : Store ctx) : Store ctx × (loadBasisInto (m := m) (ell := ell) pair output).Path :=
  let row := firstRowStep pair output store
  let powers := powerRowsStep m ell output row.1
  (powers.1, (row.2, powers.2))

/-- Both actual lower-row power loaders retain every original state block and its correlations. -/
theorem powerRowsInto_execute (m ell : Nat) (output : RawOutputRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (powerRowsInto m ell output).execute Reference state = state.mapClassical (fun entry =>
      let actual := powerRowsStep m ell output entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (loadPowerOfTwoInto (ell + m) output.b21)
    (loadPowerOfTwoInto (ell + m) output.b32)
    (fun before =>
      let actual := powerStep (model := model) (ell + m) output.b21 before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := powerStep (model := model) (ell + m) output.b32 before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      Word.PowerOfTwo.into_execute (ell + m) output.b21 reference current)
    (fun reference _history _ current =>
      Word.PowerOfTwo.into_execute (ell + m) output.b32 reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual source-basis loading preserves every original quantum-reference correlation. -/
theorem loadBasisInto_execute (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadBasisInto (m := m) (ell := ell) pair output).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := basisStep m ell pair output entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (loadFirstBasisRowInto pair output)
    (powerRowsInto m ell output)
    (fun before =>
      let actual := firstRowStep (model := model) pair output before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := powerRowsStep (model := model) m ell output before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      loadFirstBasisRowInto_execute pair output reference current)
    (fun reference _history _ current => powerRowsInto_execute m ell output reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis
