/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.Program.Correctness

/-!
# Actual original source-basis loading resources

The first-row formula precedes both complete initialized native power loaders.
Every actual path has exactly twice the exponent plus eight instructions and
the same serial unit-duration depth, with the original complete live context
and joint borrowed restoration.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis

open Execution
open ClassicalRoutines
open LatticeLoading

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N width : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent complete native formula for both initialized lower-row powers. -/
def powerRowsTrace (m ell width : Nat) : List (Resource.Event model) :=
  Word.PowerOfTwo.powerTrace width (ell + m) ++ Word.PowerOfTwo.powerTrace width (ell + m)

/-- Independent full source-basis instruction formula in its original execution order. -/
def basisTrace (N m ell width : Nat) : List (Resource.Event model) :=
  firstRowTrace N width ++ powerRowsTrace m ell width

/-- Every actual lower-row path emits both complete independent native power formulas. -/
lemma powerRowsInto_events (m ell : Nat) (output : RawOutputRefs ctx width)
    (path : (powerRowsInto m ell output).Path) :
    (powerRowsInto m ell output).eventTrace path = powerRowsTrace m ell width :=
  congrArg₂ List.append (Word.PowerOfTwo.into_events (ell + m) output.b21 path.1)
    (Word.PowerOfTwo.into_events (ell + m) output.b32 path.2)

/-- Every actual source-basis path emits the complete independent ordered native formula. -/
lemma loadBasisInto_events (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path) :
    (loadBasisInto (m := m) (ell := ell) pair output).eventTrace path = basisTrace N m ell width :=
  congrArg₂ List.append (loadFirstBasisRowInto_events pair output path.1)
    (powerRowsInto_events m ell output path.2)

/-- Independent complete native multiplicity budget for the original source-basis loader. -/
def basisEventEnvelope (N m ell width : Nat) : ResourcePool model :=
  ResourcePool.ofList (basisTrace N m ell width)

/-- Actual source-basis multiplicities equal the complete independent native envelope. -/
lemma loadBasisInto_resourcePool (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path) :
    (loadBasisInto (m := m) (ell := ell) pair output).resourcePool path =
      basisEventEnvelope N m ell width :=
  congrArg ResourcePool.ofList (loadBasisInto_events m ell pair output path)

/-- Both actual lower-row power loaders cost exactly twice the exponent plus four instructions. -/
lemma powerRowsInto_eventCount (m ell : Nat) (output : RawOutputRefs ctx width)
    (path : (powerRowsInto m ell output).Path) :
    ((powerRowsInto m ell output).eventTrace path).length = 2 * (ell + m) + 4 := by
  change ((Word.PowerOfTwo.into (ell + m) output.b21).eventTrace path.1 ++
    (Word.PowerOfTwo.into (ell + m) output.b32).eventTrace path.2).length = _
  rw [List.length_append]
  have second := Word.PowerOfTwo.into_eventCount (ell + m) output.b21 path.1
  have third := Word.PowerOfTwo.into_eventCount (ell + m) output.b32 path.2
  omega

/-- Actual source-basis loading costs exactly twice the exponent plus eight native instructions. -/
lemma loadBasisInto_eventCount (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path) :
    ((loadBasisInto (m := m) (ell := ell) pair output).eventTrace path).length =
      2 * (ell + m) + 8 := by
  change ((loadFirstBasisRowInto pair output).eventTrace path.1 ++
    (powerRowsInto m ell output).eventTrace path.2).length = _
  rw [List.length_append, loadFirstBasisRowInto_eventCount, powerRowsInto_eventCount]
  omega

/-- Both actual initialized lower-row powers have exactly their full serial instruction depth. -/
lemma powerRowsInto_depth (m ell : Nat) (output : RawOutputRefs ctx width)
    (path : (powerRowsInto m ell output).Path) :
    (powerRowsInto m ell output).depth (fun _ => 1) path = 2 * (ell + m) + 4 := by
  change (Word.PowerOfTwo.into (ell + m) output.b21).depth (fun _ => 1) path.1 +
    (Word.PowerOfTwo.into (ell + m) output.b32).depth (fun _ => 1) path.2 = _
  have second := Word.PowerOfTwo.into_depth (ell + m) output.b21 path.1
  have third := Word.PowerOfTwo.into_depth (ell + m) output.b32 path.2
  omega

/-- Actual source-basis dependencies have exactly the complete ordered native instruction depth. -/
lemma loadBasisInto_depth (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path) :
    (loadBasisInto (m := m) (ell := ell) pair output).depth (fun _ => 1) path =
      2 * (ell + m) + 8 := by
  change (loadFirstBasisRowInto pair output).depth (fun _ => 1) path.1 +
    (powerRowsInto m ell output).depth (fun _ => 1) path.2 = _
  rw [loadFirstBasisRowInto_depth, powerRowsInto_depth]
  omega

/-- Both actual lower-row powers restore all borrowed storage jointly with external references. -/
lemma powerRowsInto_borrowedRestored (m ell : Nat) (output : RawOutputRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (powerRowsInto m ell output).BorrowedRestored Reference state
      ((powerRowsInto m ell output).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (Word.PowerOfTwo.into_borrowedRestored (ell + m) output.b21 Reference _)
    (Word.PowerOfTwo.into_borrowedRestored (ell + m) output.b32 Reference _)

/-- Complete actual source-basis loading restores every borrowed-reference correlation jointly. -/
lemma loadBasisInto_borrowedRestored (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadBasisInto (m := m) (ell := ell) pair output).BorrowedRestored Reference state
      ((loadBasisInto (m := m) (ell := ell) pair output).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (loadFirstBasisRowInto_borrowedRestored pair output Reference _)
    (powerRowsInto_borrowedRestored m ell output Reference _)

/-- Both actual lower-row powers keep every original context entry live. -/
lemma powerRowsInto_visited (m ell : Nat) (output : RawOutputRefs ctx width)
    (path : (powerRowsInto m ell output).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (powerRowsInto m ell output).visitedContexts path) : visited = ctx := by
  change visited ∈ _ ++ _ at present
  exact (List.mem_append.mp present).elim
    (Word.PowerOfTwo.into_visited (ell + m) output.b21 path.1 visited)
    (Word.PowerOfTwo.into_visited (ell + m) output.b32 path.2 visited)

/-- Every actual source-basis instruction uses only the complete original context. -/
lemma loadBasisInto_visited (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (loadBasisInto (m := m) (ell := ell) pair output).visitedContexts path) :
    visited = ctx := by
  change visited ∈ _ ++ _ at present
  exact (List.mem_append.mp present).elim
    (loadFirstBasisRowInto_visited pair output path.1 visited)
    (powerRowsInto_visited m ell output path.2 visited)

/-- Every original resident entry remains counted during the complete actual source-basis load. -/
lemma loadBasisInto_resident_le (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path) :
    (loadBasisInto (m := m) (ell := ell) pair output).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [loadBasisInto_visited m ell pair output path visited present]

/-- Every original auxiliary role remains counted during the complete actual source-basis load. -/
lemma loadBasisInto_auxiliary_le (m ell : Nat) (pair : BatchMachine.PairRefs ctx N)
    (output : RawOutputRefs ctx width)
    (path : (loadBasisInto (m := m) (ell := ell) pair output).Path) :
    (loadBasisInto (m := m) (ell := ell) pair output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [loadBasisInto_visited m ell pair output path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBasis
