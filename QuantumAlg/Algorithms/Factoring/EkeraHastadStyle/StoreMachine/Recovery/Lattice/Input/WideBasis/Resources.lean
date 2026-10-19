/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Input.WideBasis.Correctness

/-!
# Actual wide decoding and source-basis resource composition

Both complete selected-bit decoder traces precede the initialized native basis
trace. The independent budgets include all three actual stages, preserve their
chronological dependencies and count the complete original context throughout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent chronological formula for both selected samples and the original native basis. -/
def decodeBasisTrace (N : Nat) (firstBits secondBits : List Bool) : List (Resource.Event model) :=
  (BatchMachine.decodeTrace N firstBits ++ BatchMachine.decodeTrace N secondBits) ++
    LatticeBasis.basisTrace N (shortLogBits N) (tradeoffBits N) (Width N)

/-- Every actual wide-prefix path emits the independent complete three-stage native formula. -/
lemma decodeBasisInto_events (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    (decodeBasisInto refs).eventTrace path = decodeBasisTrace N
      (BatchMachine.decodeBits refs.pair.first path.1.1)
      (BatchMachine.decodeBits refs.pair.second path.1.2) :=
  congrArg₂ List.append (BatchMachine.decodePairInto_events refs.pair path.1)
    (LatticeBasis.loadBasisInto_events (shortLogBits N) (tradeoffBits N) refs.pair refs.raw path.2)

/-- Actual wide-prefix multiplicities equal the complete independent chronological native trace. -/
lemma decodeBasisInto_resourcePool (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    (decodeBasisInto refs).resourcePool path = ResourcePool.ofList (decodeBasisTrace N
      (BatchMachine.decodeBits refs.pair.first path.1.1)
      (BatchMachine.decodeBits refs.pair.second path.1.2)) :=
  congrArg ResourcePool.ofList (decodeBasisInto_events refs path)

/-- Independent complete coordinatewise budget for both samples and the actual native basis. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  (BatchMachine.eventEnvelope N + BatchMachine.eventEnvelope N) +
    LatticeBasis.basisEventEnvelope N (shortLogBits N) (tradeoffBits N) (Width N)

/-- Actual wide initialization respects the full independent native operation-coordinate budget. -/
lemma decodeBasisInto_pool_le (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    (decodeBasisInto refs).resourcePool path ≤ eventEnvelope N := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (BatchMachine.decodePairInto_pool_le refs.pair path.1)
    (LatticeBasis.loadBasisInto_resourcePool (shortLogBits N) (tradeoffBits N)
      refs.pair refs.raw path.2).le

/-- Independent full native count allowance for both sample decoders and all basis instructions. -/
def operationBound (N : Nat) : Nat :=
  2 * (2 * measurementBits N + BatchMachine.KWidth N + 3) +
    (2 * (tradeoffBits N + shortLogBits N) + 8)

/-- Every actual wide-prefix path obeys the complete independent native operation bound. -/
lemma decodeBasisInto_eventCount_le (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    ((decodeBasisInto refs).eventTrace path).length ≤ operationBound N := by
  change ((BatchMachine.decodePairInto refs.pair).eventTrace path.1 ++
    (LatticeBasis.loadBasisInto (m := shortLogBits N) (ell := tradeoffBits N)
      refs.pair refs.raw).eventTrace path.2).length ≤ _
  rw [List.length_append]
  have decoded := BatchMachine.decodePairInto_eventCount_le refs.pair path.1
  have loaded := LatticeBasis.loadBasisInto_eventCount (shortLogBits N) (tradeoffBits N)
    refs.pair refs.raw path.2
  change _ ≤ 2 * (2 * measurementBits N + BatchMachine.KWidth N + 3) +
    (2 * (tradeoffBits N + shortLogBits N) + 8)
  omega

/-- Actual sample decoding precedes actual basis loading in the complete native dependency depth. -/
lemma decodeBasisInto_depth_le (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    (decodeBasisInto refs).depth (fun _ => 1) path ≤ operationBound N := by
  change (BatchMachine.decodePairInto refs.pair).depth (fun _ => 1) path.1 +
    (LatticeBasis.loadBasisInto (m := shortLogBits N) (ell := tradeoffBits N)
      refs.pair refs.raw).depth (fun _ => 1) path.2 ≤ _
  have decoded := BatchMachine.decodePairInto_depth_le refs.pair path.1
  have loaded := LatticeBasis.loadBasisInto_depth (shortLogBits N) (tradeoffBits N)
    refs.pair refs.raw path.2
  change _ ≤ 2 * (2 * measurementBits N + BatchMachine.KWidth N + 3) +
    (2 * (tradeoffBits N + shortLogBits N) + 8)
  omega

/-- Complete actual wide initialization restores every borrowed-reference correlation jointly. -/
lemma decodeBasisInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (decodeBasisInto refs).BorrowedRestored Reference state
      ((decodeBasisInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (BatchMachine.decodePairInto_borrowedRestored refs.pair Reference _)
    (LatticeBasis.loadBasisInto_borrowedRestored (shortLogBits N) (tradeoffBits N)
      refs.pair refs.raw Reference _)

/-- All actual wide-prefix instructions retain the complete original context. -/
lemma decodeBasisInto_visited (refs : Refs ctx N) (path : (decodeBasisInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (decodeBasisInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ _ ++ _ at present
  exact (List.mem_append.mp present).elim
    (BatchMachine.decodePairInto_visited refs.pair path.1 visited)
    (LatticeBasis.loadBasisInto_visited (shortLogBits N) (tradeoffBits N)
      refs.pair refs.raw path.2 visited)

/-- Every original resident entry is counted throughout the complete actual wide prefix. -/
lemma decodeBasisInto_resident_le (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    (decodeBasisInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [decodeBasisInto_visited refs path visited present]

/-- Every original auxiliary role is counted throughout the complete actual wide prefix. -/
lemma decodeBasisInto_auxiliary_le (refs : Refs ctx N) (path : (decodeBasisInto refs).Path) :
    (decodeBasisInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [decodeBasisInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix
