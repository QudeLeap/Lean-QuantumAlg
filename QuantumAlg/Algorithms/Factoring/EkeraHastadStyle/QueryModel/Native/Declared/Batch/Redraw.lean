/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.State
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Store

/-!
# Actual redraw of the selected declared EH batch

The next batch begins with the existing uniform residue draw and complete
parameter preparation. Both real writes and the full random/classical path
remain visible in the caller's current store and reference state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] ShorStyle.Canonical.Sampler.Program.circuit
  ShorStyle.Canonical.Sampler.Program.step

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

variable {environment : (model N).Environment}

/-- A source value determines the exact store and ordered path after redraw. -/
def redrawStep (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    Store (context base noQuantum N) × (redraw base noQuantum N).Path :=
  let source := sourceRef base noQuantum N
  let parameter := parameterRef base noQuantum N
  let prepared := ShorStyle.Canonical.Sampler.Program.step
    (model := model N) N (.storage source.toCStorageRef) parameter
    (store.write source
      (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
  (prepared.1,
    ((ShorStyle.Canonical.Sampler.PackedSample.drawPathEquiv
      (model := model N) N source).symm value, prepared.2))

/-- The real redraw writes only the original source and parameter cells. -/
lemma redraw_store (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    (redrawStep base noQuantum N store value).1 =
      (store.write (sourceRef base noQuantum N)
        (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))).write
          (parameterRef base noQuantum N) (parameterValue input value) := by
  exact ShorStyle.Canonical.Sampler.Program.samplerProgram_store
    (model := model N) input.samplerInput
    (.storage (sourceRef base noQuantum N).toCStorageRef)
    (parameterRef base noQuantum N)
    (store.write (sourceRef base noQuantum N)
      (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))) value
    (Store.read_write_same store (sourceRef base noQuantum N) _)

/-- The actual redraw keeps the entire current reference and hidden-service
state while sampling the fresh source uniformly. -/
lemma redraw_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History)) :
    (redraw base noQuantum N).execute environment Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => ((redrawStep base noQuantum N entry.1.1 entry.2).1,
          (entry.1.2.1, (entry.1.2.2,
            (redrawStep base noQuantum N entry.1.1 entry.2).2)))) := by
  refine (ShorStyle.Canonical.Sampler.Retained.sampled_sequence_execute (environment := environment)
    (model := model N) N (sourceRef base noQuantum N)
    (ShorStyle.Canonical.Sampler.Program.circuit (model := model N) N
      (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N))
    (ShorStyle.Canonical.Sampler.Program.step (model := model N) N
      (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N))
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_execute (environment := environment)
      (model := model N) N
      (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N)) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
