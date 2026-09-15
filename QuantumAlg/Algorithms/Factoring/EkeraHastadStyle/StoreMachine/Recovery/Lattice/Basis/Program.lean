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

/-- Actual initialized power loading into the original two nonzero lower-row words. -/
def powerRowsInto (m ell : Nat) (output : RawOutputRefs ctx width) : Circuit ctx ctx :=
  .seq (loadPowerOfTwoInto (ell + m) output.b21) (loadPowerOfTwoInto (ell + m) output.b32)

/-- The chronological actual lower-row power stores and complete operation paths. -/
def powerRowsStep (m ell : Nat) (output : RawOutputRefs ctx width) (store : Store ctx) :
    Store ctx × (powerRowsInto m ell output).Path :=
  let second := powerStep (ell + m) output.b21 store
  let third := powerStep (ell + m) output.b32 second.1
  (third.1, (second.2, third.2))

/-- Actual loading of the original rows `(j₁, j₂, 1)`, `(Q, 0, 0)` and `(0, Q, 0)`. -/
def loadBasisInto {m ell : Nat} (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) : Circuit ctx ctx :=
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
    (state : State ctx Reference History) :
    (powerRowsInto m ell output).execute Reference state = state.mapClassical (fun entry =>
      ((powerRowsStep m ell output entry.1).1,
        (entry.2, (powerRowsStep m ell output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (loadPowerOfTwoInto (ell + m) output.b21)
    (loadPowerOfTwoInto (ell + m) output.b32) (powerStep (ell + m) output.b21)
    (powerStep (ell + m) output.b32) (Word.PowerOfTwo.into_execute (ell + m) output.b21)
    (Word.PowerOfTwo.into_execute (ell + m) output.b32) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual source-basis loading preserves every original quantum-reference correlation. -/
theorem loadBasisInto_execute (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loadBasisInto (m := m) (ell := ell) pair output).execute Reference state =
      state.mapClassical (fun entry =>
        ((basisStep m ell pair output entry.1).1,
          (entry.2, (basisStep m ell pair output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (loadFirstBasisRowInto pair output)
    (powerRowsInto m ell output) (firstRowStep pair output) (powerRowsStep m ell output)
    (loadFirstBasisRowInto_execute pair output) (powerRowsInto_execute m ell output)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis
