/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Sample.Observation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Frame
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Probability
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Probability

/-!
# One actual EH sample jointly with an earlier retained read

The paid second pack writes the real sample slot. A separated old read carries
its complete weight through measurement and both packs, while the newly
written slot has the source conditional Born law in every reference block.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The prepared, selected, measured, packed and copied sample has its
conditional Born law jointly with any separated earlier structural read. -/
lemma body_copy_joint_reference {shape : CShape} (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position : Fin (measurementBits N),
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((Declared.body (storageContext base N) (storage_empty base noQuantum N)
        N (parameter base N)).seq (copy base noQuantum N index)).execute (sourceEnvironment
          input) Reference state)
      (fun entry _ => weight (entry.1.read observed) *
        (if entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
    ∑ original : Store (context base noQuantum N),
      (weight (original.read observed) *
        (((ShortDLP.measurement (Native.parameters N)).outcomePMF
          (ShortDLP.BornProbability.evolvedState (Native.encoding input)
            (parameterUnit (original.read
              (Native.liftInput (storageContext base N)
                (storage_empty base noQuantum N) N (parameter base N))))
            (parameterTarget (original.read
              (Native.liftInput (storageContext base N)
                (storage_empty base noQuantum N) N (parameter base N)))))
          outcome).toReal : ℂ)) *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
          ((context base noQuantum N).quantumLayout.zeroLabel, rightRef) := by
  let first := Declared.body (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)
  let advanced := first.execute (sourceEnvironment input) Reference state
  let oldWeight := fun store : Store (context base noQuantum N) => weight (store.read observed)
  let copied := fun store : Store (context base noQuantum N) =>
    oldWeight store * (if copiedValue base noQuantum N store = CShape.Value.bits outcome
      then 1 else 0)
  let working := fun store : Store (context base noQuantum N) =>
    oldWeight store * (if store.read
      (.storage (Native.resultRef (storageContext base N)
        (storage_empty base noQuantum N) N).toCStorageRef) =
      CShape.Value.bits outcome then 1 else 0)
  have sequence := Circuit.referenceFiberSum_execute_seq (environment := (sourceEnvironment
    input)) first
    (copy base noQuantum N index) state
    (fun store => oldWeight store *
      (if store.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef
  have copiedLaw := copy_joint_reference (environment := sourceEnvironment input) base
    noQuantum N index observed
    slotSeparate advanced weight outcome leftRef rightRef
  have equalAfterBody := Declared.body_reference_congr (environment := sourceEnvironment input)
    (storageContext base N) (storage_empty base noQuantum N) N
    (parameter base N) copied working (by
      intro store basis
      let measured : Store (context base noQuantum N) :=
        Declared.measuredStore (storageContext base N)
          (storage_empty base noQuantum N) N store basis
      let packed : Store (context base noQuantum N) := measured.applyOp
        (Declared.packing (storageContext base N) (storage_empty base noQuantum N) N)
      change copied packed = working packed
      dsimp only [copied, working]
      exact congrArg (fun value : (CShape.bits (measurementBits N)).Value =>
        oldWeight packed * (if value = CShape.Value.bits outcome then 1 else 0))
          (copiedValue_packed_result base noQuantum N measured)) state leftRef rightRef
  have stable (store : Store (context base noQuantum N))
      (basis : (context base noQuantum N).register.Index) :
      oldWeight ((Declared.measuredStore (storageContext base N)
        (storage_empty base noQuantum N) N store basis).applyOp
          (Declared.packing (storageContext base N) (storage_empty base noQuantum N) N)) =
        oldWeight store :=
    congrArg weight (Declared.measured_packed_frame
      (storageContext base N) (storage_empty base noQuantum N) N observed
      measuredSeparate workingSeparate store basis)
  have born := Declared.body_outcome_weighted_reference
    (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N) oldWeight stable state seeded outcome leftRef rightRef
  exact sequence.trans (copiedLaw.trans (equalAfterBody.trans born))

/-- Every later paid reset and actual copied sample retains the old structural
read jointly with its new conditional Born outcome. -/
lemma reusedSample_joint_reference {shape : CShape} (index : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (measuredSeparate : ∀ position : Fin (measurementBits N),
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        observed.storageKeys)
    (workingSeparate :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        observed.storageKeys)
    (slotSeparate : (terminalRef base noQuantum N index).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : shape.Value → ℂ) (outcome : Fin (measurementBits N) → Bool)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reusedSample base noQuantum N index).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight (entry.1.read observed) *
        (if entry.1.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
          CShape.Value.bits outcome then 1 else 0)) leftRef rightRef =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (entry.1.read observed) *
        Declared.sourceWeight N input
          (entry.1.read (Native.liftInput (storageContext base N)
            (storage_empty base noQuantum N) N (parameter base N))) outcome)
      leftRef rightRef := by
  let first := Declared.reuse (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)
  let advanced := first.execute (sourceEnvironment input) Reference state
  let oldWeight := fun store : Store (context base noQuantum N) => weight (store.read observed)
  let copied := fun store : Store (context base noQuantum N) =>
    oldWeight store * (if copiedValue base noQuantum N store = CShape.Value.bits outcome
      then 1 else 0)
  let working := fun store : Store (context base noQuantum N) =>
    oldWeight store * (if store.read
      (.storage (Native.resultRef (storageContext base N)
        (storage_empty base noQuantum N) N).toCStorageRef) =
      CShape.Value.bits outcome then 1 else 0)
  have sequence := Circuit.referenceFiberSum_execute_seq (environment := (sourceEnvironment
    input)) first
    (copy base noQuantum N index) state
    (fun store => oldWeight store *
      (if store.read (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        CShape.Value.bits outcome then 1 else 0)) leftRef rightRef
  have copiedLaw := copy_joint_reference (environment := sourceEnvironment input) base
    noQuantum N index observed
    slotSeparate advanced weight outcome leftRef rightRef
  have equalAfterReuse := Declared.reuse_reference_congr (environment := sourceEnvironment input)
    (storageContext base N) (storage_empty base noQuantum N) N
    (parameter base N) copied working (by
      intro store basis
      let measured : Store (context base noQuantum N) :=
        Declared.measuredStore (storageContext base N)
          (storage_empty base noQuantum N) N store basis
      let packed : Store (context base noQuantum N) := measured.applyOp
        (Declared.packing (storageContext base N) (storage_empty base noQuantum N) N)
      change copied packed = working packed
      dsimp only [copied, working]
      exact congrArg (fun value : (CShape.bits (measurementBits N)).Value =>
        oldWeight packed * (if value = CShape.Value.bits outcome then 1 else 0))
          (copiedValue_packed_result base noQuantum N measured)) state leftRef rightRef
  have stable (store : Store (context base noQuantum N))
      (basis : (context base noQuantum N).register.Index) :
      oldWeight ((Declared.measuredStore (storageContext base N)
        (storage_empty base noQuantum N) N store basis).applyOp
          (Declared.packing (storageContext base N) (storage_empty base noQuantum N) N)) =
        oldWeight store :=
    congrArg weight (Declared.measured_packed_frame
      (storageContext base N) (storage_empty base noQuantum N) N observed
      measuredSeparate workingSeparate store basis)
  have born := Declared.reuse_outcome_weighted_reference
    (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N) oldWeight stable state outcome leftRef rightRef
  exact sequence.trans (copiedLaw.trans (equalAfterReuse.trans born))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
