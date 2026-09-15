/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.ConstantWord.Signed

/-!
# Actual signed constant native resources
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord.Signed

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent exact event formula of the original sign-selected native unit-step loop. -/
def loopTrace (width count : Nat) (value : Int) : List (Resource.Event kind) :=
  List.replicate count (.classicalOperation (.wordUnary (opcode value) width))

/-- Independent self-XOR initialization and original signed absolute-value loop formula. -/
def nativeTrace (width : Nat) (value : Int) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .bitXor width)] ++ loopTrace width value.natAbs value

/-- Every actual unit-step loop emits exactly its independently specified instruction formula. -/
theorem loopInto_events (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (loopInto value count output).Path) :
    (loopInto value count output).eventTrace path = loopTrace width count value := by
  change (List.ofFn (fun _index : Fin count =>
    ([.classicalOperation (.wordUnary (opcode value) width)] :
      List (Resource.Event kind)))).flatten = _
  simp [loopTrace]

/-- Every actual initialized signed loader emits the complete original native formula. -/
theorem into_events (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) :
    (into value output).eventTrace path = nativeTrace width value :=
  congrArg₂ List.append rfl (loopInto_events value value.natAbs output path.2)

/-- Actual native multiplicities charge both self-initialization and the original signed loop. -/
theorem into_resourcePool (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) :
    (into value output).resourcePool path = ResourcePool.ofList (nativeTrace width value) :=
  congrArg ResourcePool.ofList (into_events value output path)

/-- Exact native count includes one self-XOR and the original number of signed unit steps. -/
theorem into_eventCount (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) :
    ((into value output).eventTrace path).length = value.natAbs + 1 := by
  rw [into_events]
  simp only [nativeTrace, loopTrace, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

/-- Actual signed unit steps have exactly their prescribed serial dependency depth. -/
theorem loopInto_depth (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (loopInto value count output).Path) :
    (loopInto value count output).depth (fun _ => 1) path = count := by
  change 0 + (∑ _index : Fin count, 1) = count
  simp

/-- Actual initialization is included in the complete signed-loader depth. -/
theorem into_depth (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) :
    (into value output).depth (fun _ => 1) path = value.natAbs + 1 := by
  change 1 + (loopInto value value.natAbs output).depth (fun _ => 1) path.2 = _
  rw [loopInto_depth]
  omega

/-- Every actual signed unit step preserves the complete original borrowed-reference state. -/
theorem loopInto_borrowedRestored (value : Int) (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loopInto value count output).BorrowedRestored Reference state
      ((loopInto value count output).execute Reference state) :=
  Circuit.borrowedRestored_iterate (.classical (stepOp value output)) Reference
    (Circuit.borrowedRestored_classical (stepOp value output)) count state

/-- Actual self-initialization and signed loading restore all borrowed-reference correlations. -/
theorem into_borrowedRestored (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into value output).BorrowedRestored Reference state
      ((into value output).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state (Circuit.borrowedRestored_classical _ state)
    (loopInto_borrowedRestored value value.natAbs output Reference _)

/-- Every actual signed-loop instruction and boundary retains the original supplied context. -/
theorem loopInto_visited (value : Int) (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (path : (loopInto value count output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (loopInto value count output).visitedContexts path) : visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun _index : Fin count => [ctx])).flatten at present
  have actual : visited = ctx ∨ count ≠ 0 ∧ visited = ctx := by simpa using present
  exact actual.elim id And.right

/-- Actual initialization and all signed loop iterations visit only the original context. -/
theorem into_visited (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (into value output).visitedContexts path) : visited = ctx := by
  change visited ∈ [ctx] ++ (loopInto value value.natAbs output).visitedContexts path.2 at present
  simp only [List.mem_append, List.mem_singleton] at present
  exact present.elim id (loopInto_visited value value.natAbs output path.2 visited)

/-- Resident accounting keeps every original quantum and classical cell live. -/
theorem into_resident_le (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) :
    (into value output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited value output path visited present]

/-- Auxiliary accounting retains original roles and adds no workspace. -/
theorem into_auxiliary_le (value : Int) (output : CWriteRef ctx (.unsignedWord width))
    (path : (into value output).Path) :
    (into value output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited value output path visited present]

end

end QuantumAlg.ClassicalRoutines.ConstantWord.Signed
