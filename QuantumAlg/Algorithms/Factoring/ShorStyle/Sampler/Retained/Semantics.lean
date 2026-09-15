/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Store

/-!
# Complete state equations for the retained sampler's real instructions

The two actual retention instructions extend the store while preserving
every quantum-reference block. The real sampled body then gives each finite
source integer equal weight and computes its exact independent output store.
The execution history records its actual native path and is not live storage.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

private theorem retain_pair_execute (ctx : RuntimeCtx kind)
    (firstKey : StorageKey) (firstShape : CShape) (firstFresh : firstKey ∉ ctx.keys)
    (secondKey : StorageKey) (secondShape : CShape)
    (secondFresh : secondKey ∉ (ctx.addRetained firstKey firstShape firstFresh).keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (Circuit.retain ctx firstKey firstShape firstFresh)
      (Circuit.retain (ctx.addRetained firstKey firstShape firstFresh)
        secondKey secondShape secondFresh)).execute Reference state =
      state.mapClassical (fun entry =>
        ((entry.1.pushRetained firstKey firstShape firstFresh).pushRetained
          secondKey secondShape secondFresh, (entry.2, ((), ())))) := by
  simp only [Circuit.execute_seq, Circuit.execute_retain, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem sampled_sequence_execute {ctx : RuntimeCtx kind} (N : Nat)
    (output : CWriteRef ctx (.bits (residueSamplingBits N))) (code : Circuit ctx ctx)
    (update : Store ctx → Store ctx × code.Path)
    (codeEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History), code.execute Reference state =
        state.mapClassical (fun entry => ((update entry.1).1, (entry.2, (update entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.seq (PackedSample.draw N output) code).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry =>
          let next := update (entry.1.1.write output (.bits (PackedSample.storedBits entry.2)))
          (next.1, (entry.1.2, (entry.2, next.2)))) := by
  let drawn : State ctx Reference (History × (PackedSample.draw N output).Path) :=
    (PackedSample.draw N output).execute Reference state
  have executed := codeEquation Reference drawn
  have regrouped := congrArg
    (fun final : State ctx Reference ((History × (PackedSample.draw N output).Path) × code.Path) =>
      final.mapHistory (fun history => (history.1.1, (history.1.2, history.2)))) executed
  refine (Circuit.execute_seq (PackedSample.draw N output) code state).trans
    (regrouped.trans ?_)
  let randomState := uniformChoice state
    (⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩ : ℕ+)
  let sampleMap : (Store ctx × History) × Fin (2 ^ residueSamplingBits N) →
      Store ctx × (History × (PackedSample.draw N output).Path) := fun entry =>
    (entry.1.1.write output (.bits (PackedSample.storedBits entry.2)), (entry.1.2, entry.2))
  let advance : Store ctx × (History × (PackedSample.draw N output).Path) →
      Store ctx × ((History × (PackedSample.draw N output).Path) × code.Path) := fun entry =>
    ((update entry.1).1, (entry.2, (update entry.1).2))
  let regroup : Store ctx × ((History × (PackedSample.draw N output).Path) × code.Path) →
      Store ctx × (History × ((PackedSample.draw N output).Path × code.Path)) := fun entry =>
    (entry.1, (entry.2.1.1, (entry.2.1.2, entry.2.2)))
  have drawLaw : drawn = randomState.mapClassical sampleMap := by
    refine (PackedSample.packedSample_draw_execute N output Reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  have firstComposition :=
    ExecutionState.executionState_mapClassical_comp drawn advance regroup
  have mappedDraw := congrArg
    (fun source : State ctx Reference (History × (PackedSample.draw N output).Path) =>
      source.mapClassical (regroup ∘ advance)) drawLaw
  have secondComposition :=
    ExecutionState.executionState_mapClassical_comp randomState sampleMap (regroup ∘ advance)
  refine Eq.trans ?_ ((firstComposition.trans (mappedDraw.trans secondComposition)).trans ?_)
  · unfold State.mapHistory
    congr 1
    · exact Subsingleton.elim _ _
    · congr 1
      exact Subsingleton.elim _ _
  · congr 1
    exact Subsingleton.elim _ _

/-- Actual allocation extends the whole store and preserves every joint quantum-reference block. -/
theorem samplerRetained_allocation_execute (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (allocation ctx N).execute Reference state =
      state.mapClassical (fun entry => (pushStore N entry.1, (entry.2, ((), ())))) := by
  exact retain_pair_execute ctx ctx.canonicalFreshKey (.bits (residueSamplingBits N))
    ctx.canonicalFreshKey_fresh (sampleContext ctx N).canonicalFreshKey
    (ParameterShape (modulusBits N)) (sampleContext ctx N).canonicalFreshKey_fresh Reference state

/-- Each actual sampled body path retains exactly one uniform fraction of every input block. -/
theorem samplerRetained_body_execute (ctx : RuntimeCtx kind) (N : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body ctx N).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => ((outcomeStep ctx N entry.1.1 entry.2).1,
          (entry.1.2, (outcomeStep ctx N entry.1.1 entry.2).2))) := by
  refine (sampled_sequence_execute N (sampleRef ctx N)
    (Program.circuit N (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N))
    (Program.step N (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N))
    (Program.samplerProgram_execute N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N)) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual body implements the independent complete output store with its uniform source law. -/
theorem samplerRetained_body_source_execute (ctx : RuntimeCtx kind) {N : Nat}
    (input : Input N) (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body ctx N).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => (outputStore input entry.1.1 entry.2,
          (entry.1.2, (outcomeStep ctx N entry.1.1 entry.2).2))) := by
  rw [samplerRetained_body_execute]
  apply congrArg (fun update =>
    (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical update)
  funext entry
  exact congrArg (fun store => (store, (entry.1.2, (outcomeStep ctx N entry.1.1 entry.2).2)))
    (samplerRetained_outcome_store input entry.1.1 entry.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
