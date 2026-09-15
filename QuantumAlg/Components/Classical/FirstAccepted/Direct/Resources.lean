/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Correctness

import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual first-success native resources without selector scratch
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native copy formula when a pending selector takes an eligible candidate. -/
def copyTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width), .classicalOperation (.bit .copy)]

private theorem eligibleArm_events (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (path : (eligibleArm eligible candidate refs value).Path) :
    (eligibleArm eligible candidate refs value).eventTrace path =
      if value.toBool then copyTrace width else [] := by
  cases value with
  | bit value => cases value <;> rfl

private theorem pendingArm_actualEvents (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pendingArm eligible candidate refs value).eventTrace
      (pendingArmStep eligible candidate refs value store).2 =
      if value.toBool then []
      else if (store.read eligible).toBool then copyTrace width else [] := by
  cases value with
  | bit value =>
      cases value
      · exact eligibleArm_events eligible candidate refs (store.read eligible)
          (eligibleArmStep eligible candidate refs (store.read eligible) store).2
      · rfl

/-- The actual selected trace contains only the two writes allowed by the original stored bits. -/
theorem into_actualEvents (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) (store : Store ctx) :
    (into eligible candidate refs).eventTrace (step eligible candidate refs store).2 =
      if (!(store.read (writeInput refs.accepted)).toBool && (store.read eligible).toBool) then
        copyTrace width else [] := by
  refine (pendingArm_actualEvents eligible candidate refs
    (store.read (writeInput refs.accepted)) store).trans ?_
  cases (store.read (writeInput refs.accepted)).toBool <;>
    cases (store.read eligible).toBool <;> rfl

/-- Every actual first-success path fits the independent allowance of one word and one bit copy. -/
theorem into_pool_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into eligible candidate refs).Path) :
    (into eligible candidate refs).resourcePool path ≤ ResourcePool.ofList (copyTrace width) := by
  rcases path with ⟨accepted, chosen⟩
  cases accepted with
  | bit acceptedBit =>
      cases acceptedBit
      · rcases chosen with ⟨eligibleValue, writes⟩
        cases eligibleValue with
        | bit eligibleBit =>
            cases eligibleBit
            · exact zero_le
            · exact le_rfl
      · exact zero_le

/-- Actual native depth charges at most the two dependent persistent writes. -/
theorem into_depth_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into eligible candidate refs).Path) :
    (into eligible candidate refs).depth (fun _ => 1) path ≤ 2 := by
  rcases path with ⟨accepted, chosen⟩
  cases accepted with
  | bit acceptedBit =>
      cases acceptedBit
      · rcases chosen with ⟨eligibleValue, writes⟩
        cases eligibleValue with
        | bit eligibleBit =>
            cases eligibleBit
            · exact Nat.zero_le 2
            · exact le_rfl
      · exact Nat.zero_le 2

/-- Actual direct selection preserves every borrowed classical value. -/
theorem step_borrowed_values (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) (store : Store ctx) :
    (step eligible candidate refs store).1.readBorrowedClassical = store.readBorrowedClassical := by
  rw [step_store]
  split
  · rfl
  · split
    · simp only [Store.readBorrowedClassical_applyOp]
    · rfl

/-- The actual direct selector restores every borrowed system jointly with arbitrary references. -/
theorem into_borrowedRestored (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into eligible candidate refs).BorrowedRestored Reference state
      ((into eligible candidate refs).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, into_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := History) (K := History × (into eligible candidate refs).Path) state
    (fun entry => ((step eligible candidate refs entry.1).1,
      (entry.2, (step eligible candidate refs entry.1).2)))
    (fun entry => step_borrowed_values eligible candidate refs entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- All actual stored-bit branches retain the original live context without any scratch
allocation. -/
theorem into_visited (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into eligible candidate refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (into eligible candidate refs).visitedContexts path) : visited = ctx := by
  rcases path with ⟨accepted, chosen⟩
  cases accepted with
  | bit acceptedBit =>
      cases acceptedBit
      · rcases chosen with ⟨eligibleValue, writes⟩
        cases eligibleValue with
        | bit eligibleBit =>
            cases eligibleBit <;>
              simpa only [into, pendingArm, eligibleArm, Circuit.visitedContexts, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false, or_self] using present
      · simpa only [into, pendingArm, Circuit.visitedContexts, List.mem_cons,
          List.not_mem_nil, or_false] using present

/-- Resident accounting retains the two persistent results and every other original resource. -/
theorem into_resident_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into eligible candidate refs).Path) :
    (into eligible candidate refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited eligible candidate refs path visited present]

/-- Auxiliary accounting retains original roles and introduces no selector work bit. -/
theorem into_auxiliary_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into eligible candidate refs).Path) :
    (into eligible candidate refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited eligible candidate refs path visited present]

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct
