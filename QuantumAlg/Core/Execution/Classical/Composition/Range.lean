/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Compose the supplied actual circuits in increasing finite-index order. -/
def forRange : (count : Nat) → (Fin count → Circuit ctx ctx) → Circuit ctx ctx
  | 0, _body => .id ctx
  | count + 1, body => .seq (body 0) (forRange count (fun index => body index.succ))

/-- Record each actual component on the store returned by its predecessor. -/
def forRangeRecord : (count : Nat) → (body : Fin count → Circuit ctx ctx) →
    (records : ∀ index, Store ctx → Store ctx × (body index).Path) →
      Store ctx → Store ctx × (forRange count body).Path
  | 0, _body, _records, store => (store, ())
  | count + 1, body, records, store =>
      sequenceRecord (body 0) (forRange count (fun index => body index.succ))
        (records 0) (forRangeRecord count (fun index => body index.succ)
          (fun index => records index.succ)) store

/-- The recorded final store is the chronological fold of the actual component store updates. -/
theorem forRangeRecord_store (count : Nat) (body : Fin count → Circuit ctx ctx)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path) (store : Store ctx) :
    (forRangeRecord count body records store).1 =
      (List.ofFn (fun index => fun current => (records index current).1)).foldl
        (fun current update => update current) store := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (forRangeRecord count (fun index => body index.succ)
        (fun index => records index.succ) (records 0 store).1).1 = _
      rw [ih, List.ofFn_succ, List.foldl_cons]

/-- Component execution equations determine the complete actual ordered-sequence record. -/
theorem execute_forRangeRecord (count : Nat) (body : Fin count → Circuit ctx ctx)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path)
    (equations : ∀ index (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (body index).execute Reference state = state.mapClassical (fun entry =>
        ((records index entry.1).1, (entry.2, (records index entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (forRange count body).execute Reference state = state.mapClassical (fun entry =>
      ((forRangeRecord count body records entry.1).1,
        (entry.2, (forRangeRecord count body records entry.1).2))) := by
  induction count generalizing Reference History with
  | zero =>
      refine (execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
  | succ count ih =>
      exact execute_sequenceRecord (body 0)
        (forRange count (fun index => body index.succ)) (records 0)
        (forRangeRecord count (fun index => body index.succ) (fun index => records index.succ))
        (equations 0) (fun reference {_} _ current =>
          ih _ _ (fun index => equations index.succ) reference current) Reference state

/-- Every actual native coordinate meets the uniform independent allowance per invocation. -/
theorem forRange_pool_le (count : Nat) (body : Fin count → Circuit ctx ctx)
    (budget : ResourcePool kind) (bounds : ∀ index path, (body index).resourcePool path ≤ budget)
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

/-- The actual native count adds the independent allowance of every indexed invocation. -/
theorem forRange_eventCount_le (count : Nat) (body : Fin count → Circuit ctx ctx) (budget : Nat)
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
theorem forRange_depth_le (count : Nat) (body : Fin count → Circuit ctx ctx) (budget : Nat)
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
theorem forRange_resident_le (count : Nat) (body : Fin count → Circuit ctx ctx)
    (budget : SpacePool kind) (entry : ctx.residentSpace ≤ budget)
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
theorem forRange_auxiliary_le (count : Nat) (body : Fin count → Circuit ctx ctx)
    (budget : SpacePool kind) (entry : ctx.auxiliarySpace ≤ budget)
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
theorem forRange_borrowedRestored (count : Nat) (body : Fin count → Circuit ctx ctx)
    (Reference : Register)
    (restored : ∀ index {History : Type} [Fintype History] (state : State ctx Reference History),
      (body index).BorrowedRestored Reference state ((body index).execute Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (forRange count body).BorrowedRestored Reference state
      ((forRange count body).execute Reference state) := by
  induction count generalizing History with
  | zero =>
      change (Circuit.id ctx).BorrowedRestored Reference state _
      rw [BorrowedRestored, observeBorrowedAfter_sameContext, forRange, execute_id]
      exact observeBorrowed_mapHistory state _
  | succ count ih =>
      apply borrowedRestored_seq
      · exact restored 0 state
      · exact ih _ (fun index => restored index.succ) _

end

end QuantumAlg.Circuit
