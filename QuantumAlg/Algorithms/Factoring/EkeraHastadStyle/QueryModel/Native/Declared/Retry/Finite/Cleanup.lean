/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution.Moments

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Probability
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Record
import all QuantumAlg.Core.Execution.Pure.Point

/-!
# Physical bank reset and completed reused EH batches

The reset measures each original bank wire and applies the selected
correction, using one scoped classical scratch cell and no extra quantum
system. It preserves retained results. The reused completed batch performs
recovery, optional selection and a paid result pack before this real reset;
its joint-state law retains the complete external reference.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The final real reset acts on all and only the original declared bank. -/
def reset : Circuit (model input) (Retry.context base noQuantum N)
    (Retry.context base noQuantum N) :=
  Declared.resetBank (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N input

/-- A further complete batch pays its own selector pack and terminal reset.
This is a real same-bank segment for the multi-batch schedule. -/
def nextCompletedCode : Circuit (model input) (Retry.context base noQuantum N)
    (Retry.context base noQuantum N) :=
  ((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N input)).seq (reset base noQuantum N input)

/-- Terminal cleanup establishes physical zero in every complete store-reference block. -/
theorem reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History)) :
    BasisSeeded.Holds (Retry.context base noQuantum N).quantumLayout.zeroLabel
      ((reset base noQuantum N input).execute Reference state) :=
  Declared.reset_seeded (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N input state

theorem seeded_recordSeed {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (seed : ctx.register.Index) (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds seed state) (label : Store ctx × History)
    (selection : Finset (Fin ctx.systemCount)) :
    (StatePromise.pure (NormalizedVector.ket
      (ctx.quantumLayout.restrictSelectedBasis selection seed))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout selection Reference
        (state.block label)) := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.observeSelection_entry]
  apply Finset.sum_eq_zero
  intro reference _
  apply Finset.sum_eq_zero
  intro complement _
  apply BasisSeeded.block_entry_zero seed state seeded label _ _ reference reference
  intro supported
  apply different
  funext wire
  exact (ctx.quantumLayout.joinSelectedBasis_selected_value
    selection row complement wire).symm.trans
    (congrFun supported.1 wire.val)

/-- The actual scoped bank reset fixes each complete output record, including
its hidden service state, history and path, at the original all-zero bank seed.
The reference block retains its own probability mass even when that mass is zero. -/
theorem reset_recordSeed {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (label : Store (Retry.context base noQuantum N) ×
      ((model input).HiddenState × (History × (reset base noQuantum N input).Path)))
    (selection : Finset (Fin (Retry.context base noQuantum N).systemCount)) :
    (StatePromise.pure (NormalizedVector.ket
      ((Retry.context base noQuantum N).quantumLayout.restrictSelectedBasis selection
        (Retry.context base noQuantum N).quantumLayout.zeroLabel))).Holds
      (DensityOperator.observeSelection
        (Retry.context base noQuantum N).quantumLayout selection Reference
        (((reset base noQuantum N input).execute Reference state).block label)) := by
  exact seeded_recordSeed _ _ (reset_seeded base noQuantum N input state)
    label selection

/-- The real terminal bank reset measures at least one physical qubit for
every modulus, including exceptional inputs. -/
theorem reset_measured (path : (reset base noQuantum N input).Path) :
    ∃ dimension : ℕ+,
      Resource.Event.measurement (model := model input) dimension ∈
        (reset base noQuantum N input).eventTrace path := by
  let storage := Batch.storageContext (Retry.callerContext base N) N
  let empty := Batch.storage_empty (Retry.callerContext base N)
    (Retry.caller_empty base noQuantum N) N
  have sameWires := Native.nativeOracle_context_wires storage empty N
  have sizeEq : (Native.context storage empty N).systemCount =
      ShortDLP.totalQubits (Native.parameters N) := by
    simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using
      congrArg List.length sameWires
  have positive : 0 < (Native.context storage empty N).systemCount := by
    rw [sizeEq]
    dsimp [ShortDLP.totalQubits, ShortDLP.firstBits, Native.parameters, shortLogBits]
    omega
  exact ZReset.BankScope.zResetBankScope_measured
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (Native.nativeOracle_context_qubits N sameWires) BitWord.model positive path

/-- Cleanup preserves each actual store-weighted reference matrix, including off-diagonal terms. -/
theorem reset_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : Store (Retry.context base noQuantum N) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reset base noQuantum N input).execute Reference state)
      (fun entry _ => weight entry.1) left right =
    ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right :=
  Declared.reset_reference (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N input state weight left right

/-- The extra paid pack leaves the persistent selector cells unchanged in
every weighted reference matrix entry. -/
theorem pack_selected_reference {Reference : Register} {History : Type}
    [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Retry.pack base noQuantum N input).execute Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right := by
  let update := fun entry : Store (Retry.context base noQuantum N) ×
      ((model input).HiddenState × History) =>
    ((Retry.packStep base noQuantum N input entry.1).1,
      (entry.2.1, (entry.2.2, (Retry.packStep base noQuantum N input entry.1).2)))
  let observe := fun store : Store (Retry.context base noQuantum N) =>
    weight (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection store)
  have executed := congrArg
    (fun output : State (Retry.context base noQuantum N) Reference
        ((model input).HiddenState × (History × (Retry.pack base noQuantum N input).Path)) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (Retry.pack_execute base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observed : (Store (Retry.context base noQuantum N) ×
        ((model input).HiddenState × History)) →
          (Retry.context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observed left right)
  funext entry basis
  have separate : (Retry.factorRef base noQuantum N).key ∉
      (Retry.selectionInput base noQuantum N).storageKeys := by
    rw [← Retry.caller_selectionInput base noQuantum N]
    exact Batch.caller_factor_separated (Retry.callerContext base N)
      (Retry.caller_empty base noQuantum N) N (Retry.originalSelectionInput base N)
  have frame := Retry.pack_frame base noQuantum N input entry.1
    (Retry.selectionInput base noQuantum N) separate
  simpa only [observe, Retry.selectedValue_selectionInput] using
    congrArg (fun selected => weight (CShape.packOption selected)) frame

/-- One further actually completed batch updates the retained first-success
factor with the original source law. The equality retains every reference
matrix entry and every incoming store and service-history branch, including
zero-weight branches. -/
theorem nextCompleted_reference {Reference : Register} {History : Type}
    [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextCompletedCode base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
            (Batch.SourceRecovery.packedValue output)))
      left right := by
  let observed : Store (Retry.context base noQuantum N) → ℂ :=
    fun store => weight
      (store.read (.storage (Retry.factorRef base noQuantum N).toCStorageRef))
  let preceding := (Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N input)
  calc
    _ = ExecutionState.referenceFiberSum
        ((Cleanup.reset base noQuantum N input).execute Reference
          (preceding.execute Reference state))
        (fun entry _ => observed entry.1) left right :=
      Circuit.referenceFiberSum_execute_seq preceding
        (Cleanup.reset base noQuantum N input) state observed left right
    _ = ExecutionState.referenceFiberSum
        (preceding.execute Reference state)
        (fun entry _ => observed entry.1) left right :=
      reset_reference base noQuantum N input
        (preceding.execute Reference state) observed left right
    _ = ExecutionState.referenceFiberSum
        ((Retry.pack base noQuantum N input).execute Reference
          ((Retry.next base noQuantum N input).execute Reference state))
        (fun entry _ => observed entry.1) left right :=
      Circuit.referenceFiberSum_execute_seq (Retry.next base noQuantum N input)
        (Retry.pack base noQuantum N input) state observed left right
    _ = ExecutionState.referenceFiberSum
        ((Retry.next base noQuantum N input).execute Reference state)
        (fun entry _ => weight (Optional.selectedValue
          (Retry.selectionRefs base noQuantum N).selection entry.1))
        left right :=
      Retry.pack_reference base noQuantum N input
        ((Retry.next base noQuantum N input).execute Reference state) weight left right
    _ = _ := Retry.next_selected_reference base noQuantum N input state normalized
      weight left right

/-- The completed later batch leaves the persistent first-success selector
with the same weighted transition law. Its added pack and physical reset do
not erase the value needed by a subsequent actual batch. -/
theorem nextCompleted_selected_reference {Reference : Register} {History : Type}
    [Fintype History]
    (state : State (Retry.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextCompletedCode base noQuantum N input).execute Reference state)
      (fun entry _ => weight (Optional.selectedValue
        (Retry.selectionRefs base noQuantum N).selection entry.1)) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (Optional.retainValue
            (Optional.selectedValue (Retry.selectionRefs base noQuantum N).selection entry.1)
            (Batch.SourceRecovery.packedValue output)))
      left right := by
  let observed : Store (Retry.context base noQuantum N) → ℂ :=
    fun store => weight (Optional.selectedValue
      (Retry.selectionRefs base noQuantum N).selection store)
  let preceding := (Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N input)
  calc
    _ = ExecutionState.referenceFiberSum
        ((Cleanup.reset base noQuantum N input).execute Reference
          (preceding.execute Reference state))
        (fun entry _ => observed entry.1) left right :=
      Circuit.referenceFiberSum_execute_seq preceding
        (Cleanup.reset base noQuantum N input) state observed left right
    _ = ExecutionState.referenceFiberSum
        (preceding.execute Reference state)
        (fun entry _ => observed entry.1) left right :=
      reset_reference base noQuantum N input
        (preceding.execute Reference state) observed left right
    _ = ExecutionState.referenceFiberSum
        ((Retry.pack base noQuantum N input).execute Reference
          ((Retry.next base noQuantum N input).execute Reference state))
        (fun entry _ => observed entry.1) left right :=
      Circuit.referenceFiberSum_execute_seq (Retry.next base noQuantum N input)
        (Retry.pack base noQuantum N input) state observed left right
    _ = ExecutionState.referenceFiberSum
        ((Retry.next base noQuantum N input).execute Reference state)
        (fun entry _ => observed entry.1) left right :=
      pack_selected_reference base noQuantum N input
        ((Retry.next base noQuantum N input).execute Reference state) weight left right
    _ = _ := Retry.next_selected_reference base noQuantum N input state normalized
      weight left right

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
