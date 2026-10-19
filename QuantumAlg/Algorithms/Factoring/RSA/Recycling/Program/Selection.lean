/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Complete reference observations through actual first-success selection

The existing selector reads the chronological recovered factor cells, writes
their first populated value to the retained final result and releases its
actual lexical scratch. Its actual record preserves the complete quantum
bank and both reference coordinates. No replacement selection callback or
independent probability distribution is used.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution ClassicalRoutines

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The complete final caller store identified by the actual selector's store theorem. -/
def selectionStore (before : Store (readyContext base noQuantum N count)) :
    Store (readyContext base noQuantum N count) :=
  before.write (ClassicalFrame.bankWrite noQuantum N count
    (ClassicalFrame.selectedRef base N count))
    (FirstAccepted.Direct.Optional.Allocation.value
      (fun batch => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.factorRef base N count batch))) before)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Real selection transports any complete-store weight through its original first-success write. -/
lemma rsaRecyclingParent_select_referenceFiberSum
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((select base noQuantum N count).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (selectionStore base noQuantum N count entry.1)) left right := by
  let inputs : Fin count → CInputRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    fun batch => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.factorRef base N count batch))
  let output : CWriteRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.selectedRef base N count)
  let update := fun entry : Store (readyContext base noQuantum N count) ×
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History) =>
    let actual := FirstAccepted.Direct.Optional.Allocation.step (environment := environment)
      (model := ShortDLP.CompiledMAU.Recycling.model) inputs output (entry.1, entry.2.1)
    (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))
  have executed : (select base noQuantum N count).execute environment Reference state =
      state.mapClassical update :=
    FirstAccepted.Direct.Optional.Allocation.into_execute (environment := environment)
      (model := ShortDLP.CompiledMAU.Recycling.model) inputs output Reference state
  have observed := congrArg (fun result => ExecutionState.referenceFiberSum result
    (fun entry _ => weight entry.1) left right) executed
  refine observed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => weight entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store (readyContext base noQuantum N count) ×
        (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) →
        (readyContext base noQuantum N count).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (FirstAccepted.Direct.Optional.Allocation.into_store (environment :=
    environment)
    (model := ShortDLP.CompiledMAU.Recycling.model) inputs output (entry.1, entry.2.1))

/-- The actual classical selector leaves every complete final block at the same physical seed. -/
lemma rsaRecyclingParent_select_seeded
    (seed : (readyContext base noQuantum N count).register.Index)
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed ((select base noQuantum N count).execute environment Reference
      state) := by
  let inputs : Fin count → CInputRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    fun batch => FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.factorRef base N count batch))
  let output : CWriteRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.selectedRef base N count)
  let update := fun entry : Store (readyContext base noQuantum N count) ×
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History) =>
    let actual := FirstAccepted.Direct.Optional.Allocation.step (environment := environment)
      (model := ShortDLP.CompiledMAU.Recycling.model) inputs output (entry.1, entry.2.1)
    (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))
  let history := fun entry : Store (readyContext base noQuantum N count) ×
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History) =>
    let actual := FirstAccepted.Direct.Optional.Allocation.step (environment := environment)
      (model := ShortDLP.CompiledMAU.Recycling.model) inputs output (entry.1, entry.2.1)
    (actual.1.2, (entry.2.2, actual.2))
  have executed : (select base noQuantum N count).execute environment Reference state =
      state.mapClassical update :=
    FirstAccepted.Direct.Optional.Allocation.into_execute (environment := environment)
      (model := ShortDLP.CompiledMAU.Recycling.model) inputs output Reference state
  have same : state.mapClassical update = state.mapClassical
      (fun entry => (selectionStore base noQuantum N count entry.1, history entry)) := by
    apply ExecutionState.executionState_mapClassical_congr_decision
    intro entry
    apply Prod.ext
    · exact FirstAccepted.Direct.Optional.Allocation.into_store (environment := environment)
        (model := ShortDLP.CompiledMAU.Recycling.model) inputs output (entry.1, entry.2.1)
    · rfl
  rw [executed, same]
  exact BasisSeeded.mapStore seed state seeded (selectionStore base noQuantum N count) history

end

end QuantumAlg.Factoring.RSA.Recycling.Program
