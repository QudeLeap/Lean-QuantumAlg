/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Core.Base.Accounting.ResourcePool

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Construction
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Independent native event budgets of expanded GCD

Initialization emits two copies, one equality and one bit negation. Each
public iteration emits either the five explicit remainder-step events or
nothing, followed by one final copy after the schedule. All native operation
coordinates and widths are retained. The bounds follow the actual branch
paths and are independent of operand values and quantum-reference states.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

noncomputable section

open ClassicalAlgorithms.NumberTheory

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind} {width :
  Nat}

/-- Independent literal initialization ledger. -/
def initializationEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal
      width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- One fixed coordinatewise allowance for every admitted total GCD input. -/
public def nativeEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    ResourcePool model :=
  ResourcePool.ofList (initializationEvents model width) +
    (ResourcePool.scale (Euclid.gcdFuel width) (ResourcePool.ofList (remainderEvents model width)) +
      ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .copy width))))

/-- Actual initialization emits exactly the four stated native events. -/
lemma gcdInitialization_eventTrace (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (initializationBody (model := model) input first second zero active).Path) :
    (initializationBody (model := model) input first second zero active).eventTrace path =
      initializationEvents model width := by
  change (BitWord.instruction (execution := model)
    (.wordUnary .copy width ctx (.first input) first)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model)
        (.wordUnary .copy width ctx (.second input) second)).eventTrace path.2.1 ++
          ((BitWord.instruction (execution := model)
            (testActiveOp first zero active)).eventTrace path.2.2.1 ++
              (BitWord.instruction (execution := model)
                (negateActiveOp active)).eventTrace path.2.2.2)) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Actual selection charges the full five-event body exactly when its active arm is chosen. -/
lemma gcdGuardedRemainder_pool_le (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (guardedRemainder (model := model) first second zero active).Path) :
    (guardedRemainder (model := model) first second zero active).resourcePool path ≤
      ResourcePool.ofList (remainderEvents model width) := by
  rw [Circuit.resourcePool, gcdGuardedRemainder_eventTrace]
  split
  · exact le_rfl
  · exact zero_le

/-- The real finite path vector contains at most one remainder allowance per iteration. -/
lemma gcdLoop_pool_le (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) :
    ∀ path : (Circuit.iterate count (guardedRemainder (model := model) first second zero
      active)).Path,
      (Circuit.iterate count (guardedRemainder (model := model) first second zero
        active)).resourcePool path ≤
        ResourcePool.scale count (ResourcePool.ofList (remainderEvents model width)) := by
  induction count with
  | zero =>
      intro path
      exact le_rfl
  | succ count ih =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (guardedRemainder (model := model) first second zero active).eventTrace (path
          index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (gcdGuardedRemainder_pool_le first second zero active (path 0))
        (ih (fun index => path index.succ))

/-- Initialization, actual selected iterations and the final copy fit the independent ledger. -/
lemma gcdScheduled_pool_le (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (path : (scheduledBody (model := model) input first second active result).Path) :
    (scheduledBody (model := model) input first second active result).resourcePool path ≤
      nativeEnvelope model width := by
  change ResourcePool.ofList
    ((initializationBody (model := model) input first second (cellRead result) active).eventTrace
      path.1 ++ ((Circuit.iterate (Euclid.gcdFuel width)
        (guardedRemainder (model := model) first second (cellRead result) active)).eventTrace
          path.2.1 ++ (BitWord.instruction (execution := model)
            (.wordUnary .copy width ctx (cellRead second) result)).eventTrace path.2.2)) ≤ _
  rw [gcdInitialization_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (gcdLoop_pool_le first second (cellRead result) active (Euclid.gcdFuel width) path.2.1) le_rfl)

/-- Real lexical allocation and release introduce no hidden arithmetic or oracle events. -/
lemma gcdLexical_pool_le (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width))
    (path : (lexicalBody (model := model) input result).Path) :
    (lexicalBody (model := model) input result).resourcePool path ≤ nativeEnvelope model width :=
  gcdScheduled_pool_le (underLoop input width) (currentCell ctx width) (previousCell ctx width)
    (conditionCell ctx width) (writeUnderLoop result width) path

/-- The full retained GCD circuit satisfies the same independent native coordinate budget. -/
lemma gcdRetained_pool_le (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit (model := model) input key fresh).Path) :
    (retainedCircuit (model := model) input key fresh).resourcePool path ≤ nativeEnvelope model
      width :=
  gcdLexical_pool_le (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh) path.2

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
