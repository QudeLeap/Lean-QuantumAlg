/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Resources

/-!
# Actual initialization of the original first-success latch
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelectorInit

open Execution
open ClassicalRoutines.FirstAccepted.Direct (Refs writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original actual self-XOR clears only the persistent accepted latch. -/
def clearOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .xor ctx (.product (writeInput refs.accepted) (writeInput refs.accepted)) refs.accepted

/-- Initialize the original first-success predicate by one actual native Boolean operation. -/
def clearAcceptedInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  BitWord.instruction (execution := model) (clearOp refs)

/-- The complete actual initialized caller store and its native instruction path. -/
def clearStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (clearAcceptedInto refs).Path :=
  BitWord.instructionStep (execution := model) (clearOp refs) store

/-- Actual latch initialization retains all incoming histories and quantum-reference blocks. -/
lemma clearAcceptedInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (clearAcceptedInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := clearStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  BitWord.bitWord_instruction_execute (environment := environment) (clearOp refs) state

/-- The original accepted latch becomes false from every actual incoming value. -/
lemma clearAcceptedInto_correct (refs : Refs ctx width) (store : Store ctx) :
    (clearStep refs store).1.read (writeInput refs.accepted) = .bit false := by
  refine (Store.read_applyOp_output store (clearOp refs)).trans ?_
  change Resource.BitOpcode.eval .xor
    (.product (store.read (writeInput refs.accepted)) (store.read (writeInput refs.accepted))) = _
  cases store.read (writeInput refs.accepted) with
  | bit value => cases value <;> rfl

/-- Actual initialization retains every caller read outside the persistent accepted cell. -/
lemma clearAcceptedInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.accepted.key ∉ other.storageKeys) :
    (clearStep refs store).1.read other = store.read other :=
  Store.read_applyOp_of_not_mem_storageKeys store (clearOp refs) other avoids

/-- Independent original one-XOR native allowance for initializing first-success selection. -/
def clearAcceptedEventEnvelope (model : ExecutionModel) [BitWord.Selected model] :
    ResourcePool model :=
  ResourcePool.singleton (.classicalOperation
    (BitWord.selectedCoordinate (execution := model) (.bit .xor)))

/-- Every actual initialization path emits exactly its original one-XOR native pool. -/
lemma clearAcceptedInto_resourcePool (refs : Refs ctx width)
    (path : (clearAcceptedInto refs).Path) :
    (clearAcceptedInto refs).resourcePool path = clearAcceptedEventEnvelope model := by
  change (BitWord.instruction (execution := model) (clearOp refs)).Path at path
  change ResourcePool.ofList ((clearAcceptedInto refs).eventTrace path) = _
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (clearOp refs)).eventTrace path) = _
  rw [BitWord.bitWord_instruction_eventTrace]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  rfl

/-- The actual original initialization consumes exactly one native unit duration. -/
lemma clearAcceptedInto_depth (refs : Refs ctx width) (path : (clearAcceptedInto refs).Path) :
    (clearAcceptedInto refs).depth (fun _ => 1) path = 1 := by
  change (BitWord.instruction (execution := model) (clearOp refs)).Path at path
  change (BitWord.instruction (execution := model) (clearOp refs)).depth (fun _ => 1) path = 1
  rw [BitWord.bitWord_instruction_depth]

/-- Actual latch initialization restores every borrowed correlation with arbitrary references. -/
lemma clearAcceptedInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (clearAcceptedInto refs).BorrowedRestored Reference state
      ((clearAcceptedInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_classical (environment := environment) (model := model)
    (BitWord.selectedApplication (execution := model) (clearOp refs)) state

/-- Original resident storage remains counted during the actual initialization instruction. -/
lemma clearAcceptedInto_resident_le (refs : Refs ctx width)
    (path : (clearAcceptedInto refs).Path) :
    (clearAcceptedInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  change visited ∈ [ctx] at present
  rw [List.mem_singleton.mp present]

/-- Original auxiliary roles remain counted, with no added selector work bit. -/
lemma clearAcceptedInto_auxiliary_le (refs : Refs ctx width)
    (path : (clearAcceptedInto refs).Path) :
    (clearAcceptedInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  change visited ∈ [ctx] at present
  rw [List.mem_singleton.mp present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateSelectorInit
