/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

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

open ClassicalAlgorithms.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent literal initialization ledger. -/
def initializationEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordBinary .equal width),
    .classicalOperation (.bit .not)]

/-- One fixed coordinatewise allowance for every admitted total GCD input. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (initializationEvents kind width) +
    (ResourcePool.scale (Euclid.gcdFuel width) (ResourcePool.ofList (remainderEvents kind width)) +
      ResourcePool.singleton (.classicalOperation (.wordUnary .copy width)))

/-- Actual initialization emits exactly the four stated native events. -/
theorem gcdInitialization_eventTrace (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (initializationBody input first second zero active).Path) :
    (initializationBody input first second zero active).eventTrace path =
      initializationEvents kind width := rfl

/-- Actual selection charges the full five-event body exactly when its active arm is chosen. -/
theorem gcdGuardedRemainder_pool_le (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (guardedRemainder first second zero active).Path) :
    (guardedRemainder first second zero active).resourcePool path ≤
      ResourcePool.ofList (remainderEvents kind width) := by
  rw [Circuit.resourcePool, gcdGuardedRemainder_eventTrace]
  split
  · exact le_rfl
  · exact zero_le

/-- The real finite path vector contains at most one remainder allowance per iteration. -/
theorem gcdLoop_pool_le (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) :
    ∀ path : (Circuit.iterate count (guardedRemainder first second zero active)).Path,
      (Circuit.iterate count (guardedRemainder first second zero active)).resourcePool path ≤
        ResourcePool.scale count (ResourcePool.ofList (remainderEvents kind width)) := by
  induction count with
  | zero =>
      intro path
      exact le_rfl
  | succ count ih =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (guardedRemainder first second zero active).eventTrace (path index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (gcdGuardedRemainder_pool_le first second zero active (path 0))
        (ih (fun index => path index.succ))

/-- Initialization, actual selected iterations and the final copy fit the independent ledger. -/
theorem gcdScheduled_pool_le (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (path : (scheduledBody input first second active result).Path) :
    (scheduledBody input first second active result).resourcePool path ≤
      nativeEnvelope kind width := by
  change ResourcePool.ofList (initializationEvents kind width ++
      ((Circuit.iterate (Euclid.gcdFuel width)
        (guardedRemainder first second (cellRead result) active)).eventTrace path.2.1 ++
        [.classicalOperation (.wordUnary .copy width)])) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add
    (gcdLoop_pool_le first second (cellRead result) active (Euclid.gcdFuel width) path.2.1) le_rfl)

/-- Real lexical allocation and release introduce no hidden arithmetic or oracle events. -/
theorem gcdLexical_pool_le (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width))
    (path : (lexicalBody input result).Path) :
    (lexicalBody input result).resourcePool path ≤ nativeEnvelope kind width :=
  gcdScheduled_pool_le (underLoop input width) (currentCell ctx width) (previousCell ctx width)
    (conditionCell ctx width) (writeUnderLoop result width) path

/-- The full retained GCD circuit satisfies the same independent native coordinate budget. -/
theorem gcdRetained_pool_le (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (retainedCircuit input key fresh).Path) :
    (retainedCircuit input key fresh).resourcePool path ≤ nativeEnvelope kind width :=
  gcdLexical_pool_le (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh) path.2

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
