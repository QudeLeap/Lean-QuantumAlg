/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Persistent latch values of actual first-accepted selection

Separation describes the identities of supplied writable cells and the keys
read by the two inputs. Concrete enclosing layouts discharge these internal
facts. Both scratch bits may share one cell. No scratch initialization is
needed: the two real Boolean operations overwrite their actual values first.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural separation used only to derive the persistent latch specification. -/
structure Separated (inputs : Inputs ctx width) (refs : Refs ctx width) : Prop where
  /-- Availability is read before eligibility is consumed. -/
  availableEligible : refs.available.key ∉ inputs.eligible.storageKeys
  /-- Neither scratch write changes the candidate before it is copied. -/
  availableCandidate : refs.available.key ∉ inputs.candidate.storageKeys
  takeCandidate : refs.take.key ∉ inputs.candidate.storageKeys
  /-- Scratch writes preserve the two persistent latches. -/
  availableAccepted : refs.available.key ≠ refs.accepted.key
  takeAccepted : refs.take.key ≠ refs.accepted.key
  availableSelected : refs.available.key ≠ refs.selected.key
  takeSelected : refs.take.key ≠ refs.selected.key
  /-- The final latch copy preserves the selected word. -/
  acceptedSelected : refs.accepted.key ≠ refs.selected.key

private theorem preserves_cell {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ other.key) (store : Store ctx) :
    (store.applyOp op).read (cellRead other) = store.read (cellRead other) :=
  Store.read_write_other store op.outputRef other.toCStorageRef _ different

private theorem available_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (availableOp refs)).read (cellRead refs.available)).toBool =
      !(store.read (cellRead refs.accepted)).toBool := by
  have actual := congrArg CShape.Value.toBool
    (Store.read_applyOp_output store (availableOp refs))
  change ((store.applyOp (availableOp refs)).read (cellRead refs.available)).toBool =
    ((availableOp refs).eval (store.read (cellRead refs.accepted))).toBool at actual
  cases value : store.read (cellRead refs.accepted) with
  | bit bit =>
      rw [value] at actual
      exact actual

private theorem take_read (inputs : Inputs ctx width) (refs : Refs ctx width)
    (store : Store ctx) :
    ((store.applyOp (takeOp inputs refs)).read (cellRead refs.take)).toBool =
      ((store.read (cellRead refs.available)).toBool && (store.read inputs.eligible).toBool) := by
  have actual := congrArg CShape.Value.toBool
    (Store.read_applyOp_output store (takeOp inputs refs))
  change ((store.applyOp (takeOp inputs refs)).read (cellRead refs.take)).toBool =
    ((takeOp inputs refs).eval (.product
      (store.read (cellRead refs.available)) (store.read inputs.eligible))).toBool at actual
  cases left : store.read (cellRead refs.available) with
  | bit available =>
      cases right : store.read inputs.eligible with
      | bit eligible =>
          rw [left, right] at actual
          exact actual

private theorem accepted_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (acceptedCopyOp refs)).read (cellRead refs.accepted)).toBool =
      (store.read (cellRead refs.take)).toBool := by
  have actual := congrArg CShape.Value.toBool
    (Store.read_applyOp_output store (acceptedCopyOp refs))
  change ((store.applyOp (acceptedCopyOp refs)).read (cellRead refs.accepted)).toBool =
    ((acceptedCopyOp refs).eval (store.read (cellRead refs.take))).toBool at actual
  cases value : store.read (cellRead refs.take) with
  | bit bit =>
      rw [value] at actual
      exact actual

/-- The actual decision bit is the conjunction of availability and original eligibility. -/
theorem firstAccepted_decision_take (inputs : Inputs ctx width) (refs : Refs ctx width)
    (availableEligible : refs.available.key ∉ inputs.eligible.storageKeys) (store : Store ctx) :
    ((decisionStore inputs refs store).read (cellRead refs.take)).toBool =
      ((!(store.read (cellRead refs.accepted)).toBool) &&
        (store.read inputs.eligible).toBool) := by
  unfold decisionStore
  rw [take_read, available_read,
    Store.read_applyOp_of_not_mem_storageKeys _ (availableOp refs)
      inputs.eligible availableEligible]

private theorem latch_when_taken (accepted eligible : Bool)
    (taken : ((!accepted) && eligible) = true) :
    ((!accepted) && eligible) = (accepted || eligible) := by
  cases accepted <;> cases eligible <;> simp_all

private theorem latch_when_skipped (accepted eligible : Bool)
    (skipped : ((!accepted) && eligible) ≠ true) : accepted = (accepted || eligible) := by
  cases accepted <;> cases eligible <;> simp_all

/-- The latch becomes an OR fold, and the selected word changes only on first acceptance. -/
theorem firstAccepted_latches (inputs : Inputs ctx width) (refs : Refs ctx width)
    (separated : Separated inputs refs) (store : Store ctx) :
    let final := (step inputs refs store).1
    (final.read (cellRead refs.accepted)).toBool =
        ((store.read (cellRead refs.accepted)).toBool || (store.read inputs.eligible).toBool) ∧
      final.read (cellRead refs.selected) =
        if (!(store.read (cellRead refs.accepted)).toBool) &&
            (store.read inputs.eligible).toBool then
          store.read inputs.candidate else store.read (cellRead refs.selected) := by
  let decision := decisionStore inputs refs store
  have decisionAccepted : decision.read (cellRead refs.accepted) =
      store.read (cellRead refs.accepted) :=
    (preserves_cell (takeOp inputs refs) refs.accepted separated.takeAccepted _).trans
      (preserves_cell (availableOp refs) refs.accepted separated.availableAccepted store)
  have decisionSelected : decision.read (cellRead refs.selected) =
      store.read (cellRead refs.selected) :=
    (preserves_cell (takeOp inputs refs) refs.selected separated.takeSelected _).trans
      (preserves_cell (availableOp refs) refs.selected separated.availableSelected store)
  have decisionCandidate : decision.read inputs.candidate = store.read inputs.candidate :=
    (Store.read_applyOp_of_not_mem_storageKeys _ (takeOp inputs refs) inputs.candidate
      separated.takeCandidate).trans
      (Store.read_applyOp_of_not_mem_storageKeys _ (availableOp refs) inputs.candidate
        separated.availableCandidate)
  have decisionTake := firstAccepted_decision_take inputs refs separated.availableEligible store
  have copyAccepted : ((copyStore inputs refs decision).read (cellRead refs.accepted)).toBool =
      (decision.read (cellRead refs.take)).toBool := by
    unfold copyStore
    rw [accepted_read,
      preserves_cell (selectedCopyOp inputs refs) refs.take separated.takeSelected.symm]
  have copySelected : (copyStore inputs refs decision).read (cellRead refs.selected) =
      store.read inputs.candidate := by
    unfold copyStore
    rw [preserves_cell (acceptedCopyOp refs) refs.selected separated.acceptedSelected]
    exact (Store.read_applyOp_output decision (selectedCopyOp inputs refs)).trans decisionCandidate
  dsimp only
  rw [firstAccepted_step_store]
  by_cases taken : (decision.read (cellRead refs.take)).toBool = true
  · rw [if_pos taken]
    refine ⟨?_, ?_⟩
    · rw [copyAccepted, decisionTake]
      exact latch_when_taken _ _ (decisionTake.symm.trans taken)
    · rw [← decisionTake, if_pos taken]
      exact copySelected
  · rw [if_neg taken]
    refine ⟨?_, ?_⟩
    · rw [decisionAccepted]
      have skipped : ((!(store.read (cellRead refs.accepted)).toBool) &&
          (store.read inputs.eligible).toBool) ≠ true := by
        rw [← decisionTake]
        exact taken
      exact latch_when_skipped _ _ skipped
    · rw [← decisionTake, if_neg taken]
      exact decisionSelected

end QuantumAlg.ClassicalRoutines.FirstAccepted
