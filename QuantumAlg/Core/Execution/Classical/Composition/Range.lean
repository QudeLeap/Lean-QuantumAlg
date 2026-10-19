/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Composition.Record
public import QuantumAlg.Core.Execution.Circuit.Restoration
public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual indexed finite sequences

An indexed sequence contains the existing circuits in increasing finite-index
order. Its record follows their actual intermediate stores and paths; the
interpreter equation requires each body's complete actual execution equation.
Native events add in order, while resident and auxiliary storage take maxima.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
variable {allowAllocation : Bool}

/-- Compose the supplied actual circuits in increasing finite-index order. -/
@[expose] public def forRange :
    (count : Nat) → (Fin count → Circuit model ctx ctx allowAllocation) →
      Circuit model ctx ctx allowAllocation
  | 0, _body => .id (model := model) ctx
  | count + 1, body => .seq (body 0) (forRange count (fun index => body index.succ))

/-- Record each component on the actual store and service state returned by its predecessor. -/
@[expose] public def forRangeRecord : (count : Nat) →
    (body : Fin count → Circuit model ctx ctx allowAllocation) →
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path) →
      Store ctx × model.HiddenState →
        (Store ctx × model.HiddenState) × (forRange count body).Path
  | 0, _body, _records, entry => (entry, ())
  | count + 1, body, records, entry =>
      sequenceRecord (body 0) (forRange count (fun index => body index.succ))
        (records 0) (forRangeRecord count (fun index => body index.succ)
          (fun index => records index.succ)) entry

/-- The chronological fold retains both the actual caller store and persistent service state. -/
public lemma forRangeRecord_state (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path)
    (entry : Store ctx × model.HiddenState) :
    (forRangeRecord count body records entry).1 =
      (List.ofFn (fun index => fun current => (records index current).1)).foldl
        (fun current update => update current) entry := by
  induction count generalizing entry with
  | zero => rfl
  | succ count ih =>
      change (forRangeRecord count (fun index => body index.succ)
        (fun index => records index.succ) (records 0 entry).1).1 = _
      rw [ih, List.ofFn_succ, List.foldl_cons]

/-- Caller storage is the store projection of that same chronological state fold. -/
public lemma forRangeRecord_store (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path)
    (entry : Store ctx × model.HiddenState) :
    (forRangeRecord count body records entry).1.1 =
      ((List.ofFn (fun index => fun current => (records index current).1)).foldl
        (fun current update => update current) entry).1 :=
  congrArg Prod.fst (forRangeRecord_state count body records entry)

/-- Record a range of caller-store updates that retain the selected model's service state. -/
@[expose] public def forRangeStoreRecord (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path) :
    Store ctx → Store ctx × (forRange count body).Path :=
  match count with
  | 0 => fun store => (store, ())
  | count + 1 => fun store =>
      sequenceStoreRecord (body 0) (forRange count (fun index => body index.succ))
        (records 0) (forRangeStoreRecord count (fun index => body index.succ)
          (fun index => records index.succ)) store

/-- Store-only range records have the same chronological caller-store fold. -/
public lemma forRangeStoreRecord_store (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path) (store : Store ctx) :
    (forRangeStoreRecord count body records store).1 =
      (List.ofFn (fun index => fun current => (records index current).1)).foldl
        (fun current update => update current) store := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (forRangeStoreRecord count (fun index => body index.succ)
        (fun index => records index.succ) (records 0 store).1).1 = _
      rw [ih, List.ofFn_succ, List.foldl_cons]

/-- Component equations determine the complete record and current service state at each slot. -/
lemma execute_forRangeRecord (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (environment : model.Environment)
    (records : ∀ index, Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (body index).Path)
    (equations : ∀ index (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (body index).execute environment Reference state = state.mapClassical (fun entry =>
        let result := records index (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (forRange count body).execute environment Reference state = state.mapClassical (fun entry =>
      let result := forRangeRecord count body records (entry.1, entry.2.1)
      (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  induction count generalizing Reference History with
  | zero =>
      exact (execute_id_mapClassical (allowAllocation := allowAllocation)
        (model := model) (environment := environment) Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ count ih =>
      exact execute_sequenceRecord (body 0)
        (forRange count (fun index => body index.succ)) environment (records 0)
        (forRangeRecord count (fun index => body index.succ) (fun index => records index.succ))
        (equations 0) (fun reference {_} _ current =>
          ih _ _ (fun index => equations index.succ) reference current) Reference state

/-- Store-only component equations determine a range while preserving service state. -/
lemma execute_forRangeStoreRecord (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (environment : model.Environment)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path)
    (equations : ∀ index (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (body index).execute environment Reference state = state.mapClassical (fun entry =>
        let result := records index entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (forRange count body).execute environment Reference state = state.mapClassical (fun entry =>
      let result := forRangeStoreRecord count body records entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  induction count generalizing Reference History with
  | zero =>
      exact (execute_id_mapClassical (allowAllocation := allowAllocation)
        (model := model) (environment := environment) Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ count ih =>
      exact execute_sequenceStoreRecord (body 0)
        (forRange count (fun index => body index.succ)) environment (records 0)
        (forRangeStoreRecord count (fun index => body index.succ)
          (fun index => records index.succ))
        (equations 0) (fun reference {_} _ current =>
          ih (fun index => body index.succ) (fun index => records index.succ)
            (fun index => equations index.succ) reference current) Reference state

/-- Every actual resource coordinate meets the uniform independent allowance per invocation. -/
public lemma forRange_pool_le (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (budget : ResourcePool model) (bounds : ∀ index path, (body index).resourcePool path ≤ budget)
    (path : (forRange count body).Path) :
    (forRange count body).resourcePool path ≤ ResourcePool.scale count budget := by
  induction count with
  | zero => exact le_rfl
  | succ count ih =>
      change ResourcePool.ofList ((body 0).eventTrace path.1 ++
        (forRange count (fun index => body index.succ)).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (bounds 0 path.1)
        (ih _ (fun index => bounds index.succ) path.2)

/-- The event count adds each indexed invocation's independent allowance. -/
public lemma forRange_eventCount_le (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (budget : Nat)
    (bounds : ∀ index path, ((body index).eventTrace path).length ≤ budget)
    (path : (forRange count body).Path) :
    ((forRange count body).eventTrace path).length ≤ count * budget := by
  induction count with
  | zero => simp [forRange, Circuit.eventTrace]
  | succ count ih =>
      change ((body 0).eventTrace path.1 ++
        (forRange count (fun index => body index.succ)).eventTrace path.2).length ≤ _
      rw [List.length_append, Nat.succ_mul, Nat.add_comm (count * budget)]
      exact Nat.add_le_add (bounds 0 path.1)
        (ih _ (fun index => bounds index.succ) path.2)

/-- Every actual path includes all indexed dependency depths in their original order. -/
public lemma forRange_depth_le (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (budget : Nat)
    (bounds : ∀ index path, (body index).depth (fun _ => 1) path ≤ budget)
    (path : (forRange count body).Path) :
    (forRange count body).depth (fun _ => 1) path ≤ count * budget := by
  induction count with
  | zero => simp [forRange, Circuit.depth, Circuit.eventDepth]
  | succ count ih =>
      change (body 0).depth (fun _ => 1) path.1 +
        (forRange count (fun index => body index.succ)).depth (fun _ => 1) path.2 ≤ _
      rw [Nat.succ_mul, Nat.add_comm (count * budget)]
      exact Nat.add_le_add (bounds 0 path.1)
        (ih _ (fun index => bounds index.succ) path.2)

/-- A common resident allowance includes the entry context and every actual component scope. -/
public lemma forRange_resident_le (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (budget : SpacePool model.kind) (entry : ctx.residentSpace ≤ budget)
    (bounds : ∀ index path, (body index).peakResidentSpace path ≤ budget)
    (path : (forRange count body).Path) :
    (forRange count body).peakResidentSpace path ≤ budget := by
  induction count with
  | zero =>
      apply peakResidentSpace_le_of_visited
      intro visited present
      have same : visited = ctx := List.mem_singleton.mp present
      simpa only [same] using entry
  | succ count ih =>
      refine (peakResidentSpace_seq (body 0)
        (forRange count (fun index => body index.succ)) path).le.trans ?_
      exact SpacePool.max_le (bounds 0 path.1)
        (ih _ (fun index => bounds index.succ) path.2)

/-- A common auxiliary allowance includes the entry roles and every actual component scope. -/
public lemma forRange_auxiliary_le (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (budget : SpacePool model.kind) (entry : ctx.auxiliarySpace ≤ budget)
    (bounds : ∀ index path, (body index).peakAuxiliarySpace path ≤ budget)
    (path : (forRange count body).Path) :
    (forRange count body).peakAuxiliarySpace path ≤ budget := by
  induction count with
  | zero =>
      apply peakAuxiliarySpace_le_of_visited
      intro visited present
      have same : visited = ctx := List.mem_singleton.mp present
      simpa only [same] using entry
  | succ count ih =>
      refine (peakAuxiliarySpace_seq (body 0)
        (forRange count (fun index => body index.succ)) path).le.trans ?_
      exact SpacePool.max_le (bounds 0 path.1)
        (ih _ (fun index => bounds index.succ) path.2)

/-- Actual component restoration composes jointly with an arbitrary external reference. -/
public lemma forRange_borrowedRestored (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (restored : ∀ index {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (body index).BorrowedRestored Reference state
        ((body index).execute environment Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (forRange count body).BorrowedRestored Reference state
      ((forRange count body).execute environment Reference state) := by
  induction count generalizing History with
  | zero =>
      exact borrowedRestored_id (allowAllocation := allowAllocation) (model := model) (ctx := ctx)
        (environment := environment) (Reference := Reference) (H := History) state
  | succ count ih =>
      apply borrowedRestored_seq
      · exact restored 0 state
      · exact ih _ (fun index => restored index.succ) _

end

end QuantumAlg.Circuit
