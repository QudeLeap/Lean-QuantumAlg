/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Semantics
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.State.History

/-!
# Actual writes and complete states of fixed oracle-batch stages

The indexed slots have different real keys. Each paid pack writes exactly
one of those slots from the actual finite measurement cells. All earlier
classical storage and every quantum-reference matrix entry are retained by
the interpreter equations. Redrawing uses the real uniform source instruction
and actual parameter computation, with their complete ordered path records.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Slots

/-- Different sample indices name different actual retained cells. -/
theorem nativeOracle_sampleSlots_keys {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width count : Nat) :
    Function.Injective (fun index => (sampleRef ctx width count index).key) := by
  induction count with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right same
      revert same
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          change (samples ctx width count).canonicalFreshKey =
            (sampleRef ctx width count right).key at same
          have present := MeasurementCells.reference_key_mem
            (sampleRef ctx width count right).toCStorageRef
          exact False.elim ((samples ctx width count).canonicalFreshKey_fresh
            (same.symm ▸ present))
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          change (sampleRef ctx width count left).key =
            (samples ctx width count).canonicalFreshKey at same
          have present := MeasurementCells.reference_key_mem
            (sampleRef ctx width count left).toCStorageRef
          exact False.elim ((samples ctx width count).canonicalFreshKey_fresh
            (same ▸ present))
        · intro same
          exact congrArg Fin.succ (ih same)

attribute [local irreducible] samples

/-- The factor-result allocation changes no sample key. -/
theorem nativeOracle_terminalSlots_keys {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :
    Function.Injective (fun index => (terminalRef ctx N index).key) := by
  intro left right same
  change (sampleRef ctx (measurementBits N) 16 left).key =
    (sampleRef ctx (measurementBits N) 16 right).key at same
  exact nativeOracle_sampleSlots_keys ctx (measurementBits N) 16 same

end Slots

attribute [local irreducible] Slots.samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Structural placement beneath the bank and working result does not change the written key. -/
theorem nativeOracle_underBank_key {shape : CShape}
    (ref : CWriteRef (storageContext base N) shape) :
    (underBank base noQuantum N ref).key = ref.key := by
  unfold underBank
  exact MeasurementCells.liftWrite_key 2 _ (measurementBits N)

/-- The selected member reads exactly the same parameter cell that redraw updates. -/
theorem nativeOracle_batch_parameter_read :
    Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      (parameter base N) = .storage (parameterRef base noQuantum N).toCStorageRef := by
  let source := Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)
  let bankRef : CWriteRef
      (bankContext (storageContext base N) (storage_empty base noQuantum N) N)
      (ParameterShape N) :=
    { toCStorageRef := source.toCStorageRef.underOwnedLayout
        (storageContext base N).canonicalFreshKey (layout N)
        (storageContext base N).canonicalFreshKey_fresh
        (allocationDisjoint (storageContext base N) (storage_empty base noQuantum N) N)
      writable := source.writable }
  change (MeasurementCells.liftInput 2 (.storage bankRef.toCStorageRef)
    (measurementBits N)).underRetained
      (cellsContext (storageContext base N) (storage_empty base noQuantum N) N).canonicalFreshKey
      (.bits (measurementBits N)) _ = _
  rw [MeasurementCells.liftInput_storage 2 bankRef (measurementBits N)]
  rfl

/-- The actual final terminal references preserve the sixteen distinct preallocated keys. -/
theorem nativeOracle_batch_terminal_keys :
    Function.Injective (fun index => (terminalRef base noQuantum N index).key) := by
  intro left right same
  have oldKeys := (nativeOracle_underBank_key base noQuantum N
    (Slots.terminalRef (sourceContext base N) N left)).symm.trans
      (same.trans (nativeOracle_underBank_key base noQuantum N
        (Slots.terminalRef (sourceContext base N) N right)))
  exact Slots.nativeOracle_terminalSlots_keys (sourceContext base N) N oldKeys

/-- The copied bits come only from the actual finite measurement cells. -/
def copiedValue (store : Store (context base noQuantum N)) :
    (CShape.bits (measurementBits N)).Value :=
  CShape.packFiniteBits (measurementBits N)
    (store.read (.fixedVector fun position =>
      .storage (cells (storageContext base N) (storage_empty base noQuantum N) N
        position).toCStorageRef))

/-- One real pack updates the designated persistent slot and records its single instruction. -/
def copyStep (index : Fin 16) (store : Store (context base noQuantum N)) :
    Store (context base noQuantum N) × (copy base noQuantum N index).Path :=
  (store.write (terminalRef base noQuantum N index) (copiedValue base noQuantum N store), ())

/-- The complete actual copy execution preserves the entire quantum-reference block. -/
theorem nativeOracle_batch_copy_execute (index : Fin 16) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (copy base noQuantum N index).execute Reference state =
      state.mapClassical (fun entry => ((copyStep base noQuantum N index entry.1).1,
        (entry.2, (copyStep base noQuantum N index entry.1).2))) := by
  unfold copy
  refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Reading the destination after the actual pack returns precisely the copied finite bits. -/
theorem nativeOracle_batch_copy_read (index : Fin 16)
    (store : Store (context base noQuantum N)) :
    (copyStep base noQuantum N index store).1.read
      (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        copiedValue base noQuantum N store :=
  Store.read_write_same store _ _

/-- The paid copy leaves every other sample slot unchanged, with arbitrary earlier contents. -/
theorem nativeOracle_batch_copy_other (written observed : Fin 16) (different : written ≠ observed)
    (store : Store (context base noQuantum N)) :
    (copyStep base noQuantum N written store).1.read
      (.storage (terminalRef base noQuantum N observed).toCStorageRef) =
        store.read (.storage (terminalRef base noQuantum N observed).toCStorageRef) :=
  Store.read_write_other store _ _ _
    (fun same => different (nativeOracle_batch_terminal_keys base noQuantum N same))

/-- Every structural caller input outside the destination key keeps its full actual value. -/
theorem nativeOracle_batch_copy_frame {shape : CShape} (written : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (separate : (terminalRef base noQuantum N written).key ∉ observed.storageKeys)
    (store : Store (context base noQuantum N)) :
    (copyStep base noQuantum N written store).1.read observed = store.read observed :=
  Store.read_write_of_not_mem_storageKeys store _ _ observed separate

private theorem mapped_tail {ctx : RuntimeCtx .quantum} (first second : Circuit ctx ctx)
    (step : Store ctx → Store ctx × second.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History), second.execute Reference state =
        state.mapClassical (fun entry => ((step entry.1).1, (entry.2, (step entry.1).2))))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (first.seq second).execute Reference state =
      (first.execute Reference state).mapClassical
        (fun entry => ((step entry.1).1, (entry.2.1, (entry.2.2, (step entry.1).2)))) := by
  simp only [Circuit.execute_seq, equation, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The same real reset/member state flows immediately into its paid persistent-slot write. -/
theorem nativeOracle_batch_reusedSample_execute (input : Input N) (index : Fin 16)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (reusedSample base noQuantum N input index).execute Reference state =
      ((reuse (storageContext base N) (storage_empty base noQuantum N) N input
        (parameter base N)).execute Reference state).mapClassical
          (fun entry => ((copyStep base noQuantum N index entry.1).1,
            (entry.2.1, (entry.2.2, (copyStep base noQuantum N index entry.1).2)))) :=
  mapped_tail _ (copy base noQuantum N index) (copyStep base noQuantum N index)
    (nativeOracle_batch_copy_execute base noQuantum N index) state

attribute [local irreducible] ShorStyle.Canonical.Sampler.Program.circuit
  ShorStyle.Canonical.Sampler.Program.step

/-- The real source draw and parameter program record their complete intermediate store. -/
def redrawStep (store : Store (context base noQuantum N))
    (value : Fin (2 ^ residueSamplingBits N)) :
    Store (context base noQuantum N) × (redraw base noQuantum N).Path :=
  let prepared := ShorStyle.Canonical.Sampler.Program.step N
    (.storage (sourceRef base noQuantum N).toCStorageRef) (parameterRef base noQuantum N)
    (store.write (sourceRef base noQuantum N)
      (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))
  (prepared.1, (value, prepared.2))

/-- The real redraw changes exactly the two original source and complete parameter cells. -/
theorem nativeOracle_batch_redraw_store (input : Input N)
    (store : Store (context base noQuantum N)) (value : Fin (2 ^ residueSamplingBits N)) :
    (redrawStep base noQuantum N store value).1 =
      (store.write (sourceRef base noQuantum N)
        (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))).write
          (parameterRef base noQuantum N) (parameterValue input value) :=
  ShorStyle.Canonical.Sampler.Program.samplerProgram_store input.samplerInput
    (.storage (sourceRef base noQuantum N).toCStorageRef) (parameterRef base noQuantum N)
    (store.write (sourceRef base noQuantum N)
      (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))) value
    (Store.read_write_same store (sourceRef base noQuantum N) _)

private theorem source_redraw_execute {ctx : RuntimeCtx .quantum} (N : Nat)
    (source : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    ((ShorStyle.Canonical.Sampler.PackedSample.draw N source).seq
      (ShorStyle.Canonical.Sampler.Program.circuit N
        (.storage source.toCStorageRef) parameter)).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry =>
          let prepared := ShorStyle.Canonical.Sampler.Program.step N
            (.storage source.toCStorageRef) parameter
            (entry.1.1.write source
              (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits entry.2)))
          (prepared.1, (entry.1.2, (entry.2, prepared.2)))) := by
  refine (ShorStyle.Canonical.Sampler.Retained.sampled_sequence_execute N
    source
    (ShorStyle.Canonical.Sampler.Program.circuit N
      (.storage source.toCStorageRef) parameter)
    (ShorStyle.Canonical.Sampler.Program.step N
      (.storage source.toCStorageRef) parameter)
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_execute N
      (.storage source.toCStorageRef) parameter)
    Reference state).trans ?_
  congr 1

/-- Redraw is the actual uniform source instruction followed by the actual parameter computation. -/
theorem nativeOracle_batch_redraw_execute (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (redraw base noQuantum N).execute Reference state =
      (uniformChoice state ⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩).mapClassical
        (fun entry => ((redrawStep base noQuantum N entry.1.1 entry.2).1,
          (entry.1.2, (redrawStep base noQuantum N entry.1.1 entry.2).2))) := by
  refine (source_redraw_execute N (sourceRef base noQuantum N) (parameterRef base noQuantum N)
    Reference state).trans ?_
  exact State.mapClassical_decision _ _ _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
