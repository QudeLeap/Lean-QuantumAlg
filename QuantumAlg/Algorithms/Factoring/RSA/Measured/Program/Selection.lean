/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Member
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame
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
independent probability distribution is used [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical ShortDLP.CompiledMAU.Recycling.Measured

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {environment : MeasuredRSAModel.Environment}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The complete final caller store identified by the actual selector's store theorem. -/
def selectionStore (before : Store (readyContext base noQuantum N count)) :
    Store (readyContext base noQuantum N count) :=
  before.write (bankWrite base noQuantum N count
    (Recycling.ClassicalFrame.selectedRef base N count))
    (FirstAccepted.Direct.Optional.Allocation.value
      (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
        (Recycling.ClassicalFrame.factorRef base N count batch))) before)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Real selection transports any complete-store weight through its original first-success write. -/
lemma rsaMeasuredParent_select_referenceFiberSum
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((select base noQuantum N count).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (selectionStore base noQuantum N count entry.1)) left right := by
  let inputs : Fin count → CInputRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch))
  let output : CWriteRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count)
  let update := fun entry : Store (readyContext base noQuantum N count) ×
      (MeasuredRSAModel.HiddenState × History) =>
    let actual := FirstAccepted.Direct.Optional.Allocation.step (environment := environment)
      (model := MeasuredRSAModel) inputs output (entry.1, entry.2.1)
    (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))
  have executed : (select base noQuantum N count).execute environment Reference state =
      state.mapClassical update :=
    FirstAccepted.Direct.Optional.Allocation.into_execute (environment := environment)
      (model := MeasuredRSAModel) inputs output Reference state
  have observed := congrArg (fun result => ExecutionState.referenceFiberSum result
    (fun entry _ => weight entry.1) left right) executed
  refine observed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => weight entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store (readyContext base noQuantum N count) ×
        (MeasuredRSAModel.HiddenState × History)) →
        (readyContext base noQuantum N count).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (FirstAccepted.Direct.Optional.Allocation.into_store (environment :=
    environment)
    (model := MeasuredRSAModel) inputs output (entry.1, entry.2.1))

/-- The actual classical selector leaves every complete final block at the same physical seed. -/
lemma rsaMeasuredParent_select_seeded
    (seed : (readyContext base noQuantum N count).register.Index)
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed ((select base noQuantum N count).execute environment Reference
      state) := by
  let inputs : Fin count → CInputRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.factorRef base N count batch))
  let output : CWriteRef (readyContext base noQuantum N count)
      (.option (.unsignedWord (EkeraHastadStyle.Canonical.modulusBits N))) :=
    bankWrite base noQuantum N count (Recycling.ClassicalFrame.selectedRef base N count)
  let update := fun entry : Store (readyContext base noQuantum N count) ×
      (MeasuredRSAModel.HiddenState × History) =>
    let actual := FirstAccepted.Direct.Optional.Allocation.step (environment := environment)
      (model := MeasuredRSAModel) inputs output (entry.1, entry.2.1)
    (actual.1.1, (actual.1.2, (entry.2.2, actual.2)))
  let history := fun entry : Store (readyContext base noQuantum N count) ×
      (MeasuredRSAModel.HiddenState × History) =>
    let actual := FirstAccepted.Direct.Optional.Allocation.step (environment := environment)
      (model := MeasuredRSAModel) inputs output (entry.1, entry.2.1)
    (actual.1.2, (entry.2.2, actual.2))
  have executed : (select base noQuantum N count).execute environment Reference state =
      state.mapClassical update :=
    FirstAccepted.Direct.Optional.Allocation.into_execute (environment := environment)
      (model := MeasuredRSAModel) inputs output Reference state
  have same : state.mapClassical update = state.mapClassical
      (fun entry => (selectionStore base noQuantum N count entry.1, history entry)) := by
    apply ExecutionState.executionState_mapClassical_congr_decision
    intro entry
    apply Prod.ext
    · exact FirstAccepted.Direct.Optional.Allocation.into_store (environment := environment)
        (model := MeasuredRSAModel) inputs output (entry.1, entry.2.1)
    · rfl
  rw [executed, same]
  exact BasisSeeded.mapStore seed state seeded (selectionStore base noQuantum N count) history

omit configuration in
private lemma rsaMeasuredParent_selectorValue_transport {outer inner : RuntimeCtx .quantum}
    {width : Nat} (transport : ClassicalWorkspace.Transport outer inner)
    (inputs : Fin count → CInputRef outer (.option (.unsignedWord width))) (stored : Store inner) :
    FirstAccepted.Direct.Optional.Allocation.value
      (fun index => transport.liftInput (inputs index)) stored =
      FirstAccepted.Direct.Optional.Allocation.value inputs (transport.restrict stored) := by
  have reads : (fun index => stored.read (transport.liftInput (inputs index))) =
      (fun index => (transport.restrict stored).read (inputs index)) :=
    funext fun index => transport.workspaceTransport_restrict_readsAs stored (inputs index)
  exact congrArg
    (fun read : Fin count → (CShape.option (.unsignedWord width)).Value =>
      (List.ofFn read).foldl FirstAccepted.Direct.Optional.retainValue .optionNone) reads

/-- The original first-populated factor is written into its true existing parent destination. -/
def parentSelectionStore (before : Store (Recycling.ClassicalFrame.context base N count)) :
    Store (Recycling.ClassicalFrame.context base N count) :=
  before.write (Recycling.ClassicalFrame.selectedRef base N count)
    (FirstAccepted.Direct.Optional.Allocation.value
      (fun batch => FirstAccepted.cellRead (Recycling.ClassicalFrame.factorRef base N count batch))
      before)

/-- The complete real selector update restricts to that same original parent write. -/
lemma rsaMeasuredParent_selectionStore_parent
    (before : Store (readyContext base noQuantum N count)) :
    parentStoreAt base noQuantum N count (selectionStore base noQuantum N count before) =
      parentSelectionStore base N count (parentStoreAt base noQuantum N count before) := by
  let transport := parentTransport (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
  have written := transport.workspaceTransport_restrict_write before
    (Recycling.ClassicalFrame.selectedRef base N count)
    (FirstAccepted.Direct.Optional.Allocation.value
      (fun batch => FirstAccepted.cellRead (bankWrite base noQuantum N count
        (Recycling.ClassicalFrame.factorRef base N count batch))) before)
  exact written.trans (congrArg
    (fun value => (parentStoreAt base noQuantum N count before).write
      (Recycling.ClassicalFrame.selectedRef base N count) value)
    (rsaMeasuredParent_selectorValue_transport count transport
      (fun batch => FirstAccepted.cellRead (Recycling.ClassicalFrame.factorRef base N count batch))
      before))

/-- The actual selector preserves the complete original parent/reference conditional law. -/
lemma rsaMeasuredParent_select_parent_referenceFiberSum
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((select base noQuantum N count).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (parentSelectionStore base N count
          (parentStoreAt base noQuantum N count entry.1))) left right := by
  refine (rsaMeasuredParent_select_referenceFiberSum base noQuantum N count state
    (fun stored => weight (parentStoreAt base noQuantum N count stored)) left right).trans ?_
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
  funext entry _basis
  exact congrArg weight (rsaMeasuredParent_selectionStore_parent base noQuantum N count entry.1)

end

end QuantumAlg.Factoring.RSA.Measured.Program
