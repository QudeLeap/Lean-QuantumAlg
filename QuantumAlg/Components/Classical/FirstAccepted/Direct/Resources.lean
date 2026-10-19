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

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent native copy formula when a pending selector takes an eligible candidate. -/
def copyTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .copy))]

private lemma eligibleArm_events (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (path : (eligibleArm (model := model) eligible candidate refs
      value).Path) :
    (eligibleArm (model := model) eligible candidate refs value).eventTrace path =
      if value.toBool then copyTrace (model := model) width else [] := by
  cases value with
  | bit value =>
      cases value
      · rfl
      · change (BitWord.instruction (execution := model) (selectedOp candidate refs)).eventTrace
          path.1 ++
          (BitWord.instruction (execution := model) (acceptedOp eligible refs)).eventTrace
            path.2 = _
        simp only [BitWord.bitWord_instruction_eventTrace]
        rfl

private lemma pendingArm_actualEvents (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pendingArm (model := model) eligible candidate refs value).eventTrace
      (pendingArmStep (model := model) eligible candidate refs value store).2 =
      if value.toBool then []
      else if (store.read eligible).toBool then copyTrace (model := model) width else [] := by
  cases value with
  | bit value =>
      cases value
      · exact eligibleArm_events eligible candidate refs (store.read eligible)
          (eligibleArmStep (model := model) eligible candidate refs (store.read eligible) store).2
      · rfl

/-- The actual selected trace contains only the two writes allowed by the original stored bits. -/
lemma into_actualEvents (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) (store : Store ctx) :
    (into (model := model) eligible candidate refs).eventTrace (step (model := model) eligible
      candidate refs store).2 =
      if (!(store.read (writeInput refs.accepted)).toBool && (store.read eligible).toBool) then
        copyTrace (model := model) width else [] := by
  refine (pendingArm_actualEvents eligible candidate refs
    (store.read (writeInput refs.accepted)) store).trans ?_
  cases (store.read (writeInput refs.accepted)).toBool <;>
    cases (store.read eligible).toBool <;> rfl

/-- Every actual first-success path fits the independent allowance of one word and one bit copy. -/
lemma into_pool_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into (model := model) eligible candidate refs).Path) :
    (into (model := model) eligible candidate refs).resourcePool path ≤ ResourcePool.ofList
      (copyTrace (model := model) width) := by
  rcases path with ⟨accepted, chosen⟩
  cases accepted with
  | bit acceptedBit =>
      cases acceptedBit
      · rcases chosen with ⟨eligibleValue, writes⟩
        cases eligibleValue with
        | bit eligibleBit =>
            cases eligibleBit
            · exact zero_le
            · change ResourcePool.ofList
                ((eligibleArm (model := model) eligible candidate refs (.bit true)).eventTrace
                  writes) ≤ _
              rw [eligibleArm_events]
              exact le_rfl
      · exact zero_le

/-- Actual native depth charges at most the two dependent persistent writes. -/
lemma into_depth_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into (model := model) eligible candidate refs).Path) :
    (into (model := model) eligible candidate refs).depth (fun _ => 1) path ≤ 2 := by
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
lemma step_borrowed_values (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) (store : Store ctx) :
    (step (model := model) eligible candidate refs store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [step_store]
  split
  · rfl
  · split
    · simp only [Store.readBorrowedClassical_applyOp]
    · rfl

/-- The actual direct selector restores every borrowed system jointly with arbitrary references. -/
lemma into_borrowedRestored (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) eligible candidate refs).BorrowedRestored Reference state
      ((into (model := model) eligible candidate refs).execute environment Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, into_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := model.HiddenState × History)
    (K := model.HiddenState × (History × (into (model := model) eligible candidate refs).Path))
      state
    (fun entry =>
      let actual := step (model := model) eligible candidate refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2))))
    (fun entry => step_borrowed_values eligible candidate refs entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- All actual stored-bit branches retain the original live context without any scratch
allocation. -/
lemma into_visited (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into (model := model) eligible candidate refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (into (model := model) eligible candidate refs).visitedContexts path) :
      visited = ctx := by
  rcases path with ⟨accepted, chosen⟩
  cases accepted with
  | bit acceptedBit =>
      cases acceptedBit
      · rcases chosen with ⟨eligibleValue, writes⟩
        cases eligibleValue with
        | bit eligibleBit =>
            cases eligibleBit <;>
              simpa only [into, pendingArm, eligibleArm, BitWord.instruction,
                Circuit.visitedContexts, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false, or_self] using present
      · simpa only [into, pendingArm, Circuit.visitedContexts, List.mem_cons,
          List.not_mem_nil, or_false] using present

/-- Resident accounting retains the two persistent results and every other original resource. -/
lemma into_resident_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into (model := model) eligible candidate refs).Path) :
    (into (model := model) eligible candidate refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited eligible candidate refs path visited present]

/-- Auxiliary accounting retains original roles and introduces no selector work bit. -/
lemma into_auxiliary_le (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (path : (into (model := model) eligible candidate refs).Path) :
    (into (model := model) eligible candidate refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
      by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited eligible candidate refs path visited present]

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct
