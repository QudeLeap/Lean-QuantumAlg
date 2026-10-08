/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.State
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Trace.Bounds
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual phase transitions for the fixed-fuel lattice reducer

Each transition performs one native Boolean instruction on the actual phase
bits. The original three-state encoding and every other caller read are retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePhaseControl

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The three source phase transitions selected after the actual Lovasz test. -/
inductive Transition where
  | firstPass | secondFail | secondPass
deriving DecidableEq

/-- Source phase required for the selected transition. -/
abbrev sourcePhase : Transition → NumberTheory.LLLPhase3
  | .firstPass => .first
  | .secondFail | .secondPass => .second

/-- Target phase written by the selected transition. -/
abbrev targetPhase : Transition → NumberTheory.LLLPhase3
  | .firstPass => .second
  | .secondFail => .first
  | .secondPass => .done

/-- Native Boolean opcode of each original one-instruction transition. -/
abbrev transitionOpcode : Transition → Resource.BitOpcode
  | .firstPass | .secondPass => .not
  | .secondFail => .xor

/-- The one actual bit written by the selected transition. -/
abbrev writtenRef (refs : LatticeState.MachineRefs ctx width) : Transition → CWriteRef ctx .bit
  | .firstPass | .secondFail => refs.secondPhase
  | .secondPass => refs.done

/-- Typed atomic operation reading and writing the actual phase bits. -/
def transitionOp (refs : LatticeState.MachineRefs ctx width) (transition : Transition) :
    ClassicalOp (transitionOpcode transition).inputShape .bit ctx ctx :=
  match transition with
  | .firstPass => .bit .not ctx (.storage refs.secondPhase.toCStorageRef) refs.secondPhase
  | .secondFail => .bit .xor ctx
      (.product (.storage refs.secondPhase.toCStorageRef)
        (.storage refs.secondPhase.toCStorageRef)) refs.secondPhase
  | .secondPass => .bit .not ctx (.storage refs.done.toCStorageRef) refs.done

/-- Execute the selected phase transition in the single actual circuit interpreter. -/
def transitionInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition) : Circuit model ctx ctx :=
  BitWord.instruction (execution := model) (transitionOp refs transition)

/-- Complete execution updates the actual bit and preserves history and quantum-reference blocks. -/
theorem transitionInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (transitionInto (model := model) refs transition).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := BitWord.instructionStep (execution := model)
          (transitionOp refs transition) entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  BitWord.bitWord_instruction_execute _ state

/-- Any caller read outside the selected actual bit write is unchanged. -/
theorem transitionInto_callerFrame (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : (writtenRef refs transition).key ∉ other.storageKeys) :
    (store.applyOp (transitionOp refs transition)).read other = store.read other := by
  apply Store.read_applyOp_of_not_mem_storageKeys
  cases transition <;> exact avoids

private theorem toggle_read (store : Store ctx) (output : CWriteRef ctx .bit) (value : Bool)
    (rep : (store.read (.storage output.toCStorageRef)).toBool = value) :
    ((store.applyOp (.bit .not ctx (.storage output.toCStorageRef) output)).read
      (.storage output.toCStorageRef)).toBool = !value := by
  simp only [Store.applyOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval]
  cases actual : store.read (.storage output.toCStorageRef) with
  | bit bit =>
    change (!bit) = !value
    rw [actual] at rep
    exact congrArg Bool.not rep

private theorem clear_read (store : Store ctx) (output : CWriteRef ctx .bit) :
    ((store.applyOp (.bit .xor ctx (.product (.storage output.toCStorageRef)
      (.storage output.toCStorageRef)) output)).read (.storage output.toCStorageRef)).toBool =
      false := by
  simp only [Store.applyOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval]
  change (Resource.BitOpcode.eval .xor (.product
    (store.read (.storage output.toCStorageRef))
    (store.read (.storage output.toCStorageRef)))).toBool = false
  cases actual : store.read (.storage output.toCStorageRef) with
  | bit bit => exact Bool.xor_self bit

/-- Each actual one-instruction transition realizes the original three-state phase encoding. -/
theorem transitionInto_correct (refs : LatticeState.MachineRefs ctx width)
    (separation : refs.Separated) (transition : Transition) (store : Store ctx)
    (phase : refs.PhaseRepresents store (sourcePhase transition)) :
    refs.PhaseRepresents (store.applyOp (transitionOp refs transition))
      (targetPhase transition) := by
  have distinct : refs.secondPhase.key ≠ refs.done.key := by
    intro equal
    have cells : LatticeState.MachineCell.secondPhase = .done := separation equal
    cases cells
  have doneFrame : refs.secondPhase.key ∉
      (CInputRef.storage refs.done.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using distinct
  have phaseFrame : refs.done.key ∉
      (CInputRef.storage refs.secondPhase.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using distinct.symm
  cases transition with
  | firstPass =>
    refine ⟨toggle_read store refs.secondPhase false phase.1, ?_⟩
    rw [transitionInto_callerFrame refs .firstPass store _ doneFrame]
    exact phase.2
  | secondFail =>
    refine ⟨clear_read store refs.secondPhase, ?_⟩
    rw [transitionInto_callerFrame refs .secondFail store _ doneFrame]
    exact phase.2
  | secondPass =>
    refine ⟨?_, toggle_read store refs.done false phase.2⟩
    rw [transitionInto_callerFrame refs .secondPass store _ phaseFrame]
    exact phase.1

/-- Independent native event formula of the selected phase transition. -/
def transitionTrace {model : ExecutionModel} [BitWord.Selected model]
    (transition : Transition) :
    List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.bit (transitionOpcode transition)))]

/-- The actual transition emits exactly its independent native Boolean instruction. -/
theorem transitionInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition)
    (path : (transitionInto (model := model) refs transition).Path) :
    (transitionInto (model := model) refs transition).eventTrace path =
      transitionTrace (model := model) transition := by
  dsimp only [transitionInto] at path ⊢
  rw [BitWord.bitWord_instruction_eventTrace]
  cases transition <;> rfl

/-- Native multiplicity is counted from that same independently specified operation. -/
theorem transitionInto_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition)
    (path : (transitionInto (model := model) refs transition).Path) :
    (transitionInto (model := model) refs transition).resourcePool path =
      ResourcePool.ofList (transitionTrace (model := model) transition) := by
  change ResourcePool.ofList
    ((transitionInto (model := model) refs transition).eventTrace path) = _
  rw [transitionInto_events]

/-- Each phase change has exact unit-duration dependency depth one. -/
theorem transitionInto_depth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition)
    (path : (transitionInto (model := model) refs transition).Path) :
    (transitionInto (model := model) refs transition).depth (fun _ => 1) path = 1 := by
  dsimp only [transitionInto] at path ⊢
  rw [BitWord.bitWord_instruction_depth]

/-- The phase write restores all borrowed correlations jointly with external references. -/
theorem transitionInto_borrowedRestored {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (transitionInto (model := model) refs transition).BorrowedRestored Reference state
      ((transitionInto (model := model) refs transition).execute Reference state) :=
  Circuit.borrowedRestored_classical _ state

/-- A phase change visits only the original complete caller context. -/
theorem transitionInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition)
    (path : (transitionInto (model := model) refs transition).Path) :
    (transitionInto (model := model) refs transition).visitedContexts path = [ctx] := rfl

/-- Every original resident resource remains counted during the phase write. -/
theorem transitionInto_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition)
    (path : (transitionInto (model := model) refs transition).Path) :
    (transitionInto (model := model) refs transition).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have equal : visited = ctx := by
    simpa only [transitionInto_visited, List.mem_singleton] using present
  rw [equal]

/-- Auxiliary roles remain unchanged by the phase write. -/
theorem transitionInto_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : LatticeState.MachineRefs ctx width)
    (transition : Transition)
    (path : (transitionInto (model := model) refs transition).Path) :
    (transitionInto (model := model) refs transition).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have equal : visited = ctx := by
    simpa only [transitionInto_visited, List.mem_singleton] using present
  rw [equal]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePhaseControl
