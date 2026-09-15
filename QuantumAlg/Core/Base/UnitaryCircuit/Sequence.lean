/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Accounting.Control
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Typed circuit sequences and their interpreters

`UnitarySequence R` is the single syntax tree interpreted as a unitary matrix,
a strict event pool, and a symbolic max-plus event-depth expression. No
interpreter data is stored in the tree.
-/

section

namespace QuantumAlg

open scoped BigOperators

/-- A typed construction sequence with exactly one sealed execution leaf.

The register index makes ill-typed sequential composition impossible and lets
tensor/control nodes change the register collection in their result type. The
indexed-product family deliberately remains a function `Fin count → ...`, so
regular products stay symbolic. -/
inductive UnitarySequence : Register → Type 1 where
  /-- Empty sequence over `R`. -/
  | id (R : Register) : UnitarySequence R
  /-- One gate or opaque-subroutine occurrence. -/
  | leaf {R : Register} (value : UnitaryLeaf R) : UnitarySequence R
  /-- Execute `left`, then `right`. -/
  | seq {R : Register} (left right : UnitarySequence R) : UnitarySequence R
  /-- Execute two sequences in parallel over a product register. -/
  | tensor {R S : Register} (left : UnitarySequence R) (right : UnitarySequence S) :
      UnitarySequence (Register.prod R S)
  /-- Change only the logical basis index through a certified equivalence. -/
  | reindex {R S : Register} (equiv : R.Index ≃ S.Index)
      (body : UnitarySequence R) : UnitarySequence S
  /-- Reverse the sequence and adjoint every operation semantically. -/
  | dagger {R : Register} (body : UnitarySequence R) : UnitarySequence R
  /-- Control the whole sequence at one finite-register basis value. -/
  | controlled {R : Register} (control : Register)
      (activationValue : control.Index) (body : UnitarySequence R) :
      UnitarySequence (Register.prod control R)
  /-- Symbolic fixed repetition. -/
  | iterate {R : Register} (count : Nat) (body : UnitarySequence R) : UnitarySequence R
  /-- A start sequence followed by `count` indexed steps in increasing index order. -/
  | indexedProduct {R : Register} (label : String) (count : Nat)
      (start : UnitarySequence R) (step : Fin count → UnitarySequence R) :
      UnitarySequence R

namespace UnitarySequence

noncomputable section

/-- Every gate atom in a typed sequence has a duplicate-free placement inside
the supplied circuit layout. Composite nodes require the property of every
child, including every member of an indexed-product family. -/
def AtomsContainedIn (physical_idx : List Nat) :
    {R : Register} → UnitarySequence R → Prop
  | _, .id _ => True
  | _, .leaf atom =>
      atom.systemIdx.Nodup ∧ atom.systemIdx ⊆ physical_idx
  | _, .seq left right =>
      left.AtomsContainedIn physical_idx ∧ right.AtomsContainedIn physical_idx
  | _, .tensor left right =>
      left.AtomsContainedIn physical_idx ∧ right.AtomsContainedIn physical_idx
  | _, .reindex _ body => body.AtomsContainedIn physical_idx
  | _, .dagger body => body.AtomsContainedIn physical_idx
  | _, .controlled _ _ body => body.AtomsContainedIn physical_idx
  | _, .iterate _ body => body.AtomsContainedIn physical_idx
  | _, .indexedProduct _ _ start step =>
      start.AtomsContainedIn physical_idx ∧
        ∀ j, (step j).AtomsContainedIn physical_idx

/-- Atom containment is monotone when the advertised physical layout grows. -/
theorem AtomsContainedIn.mono {physical_idx larger_idx : List Nat}
    (hlayout : physical_idx ⊆ larger_idx) {R : Register}
    {sequence : UnitarySequence R}
    (hcontained : sequence.AtomsContainedIn physical_idx) :
    sequence.AtomsContainedIn larger_idx := by
  induction sequence with
  | id => trivial
  | leaf value =>
      exact ⟨hcontained.1, fun _ hmem => hlayout (hcontained.2 hmem)⟩
  | seq left right ihLeft ihRight =>
      exact ⟨ihLeft hcontained.1, ihRight hcontained.2⟩
  | tensor left right ihLeft ihRight =>
      exact ⟨ihLeft hcontained.1, ihRight hcontained.2⟩
  | reindex equiv body ih => exact ih hcontained
  | dagger body ih => exact ih hcontained
  | controlled control activationValue body ih => exact ih hcontained
  | iterate count body ih => exact ih hcontained
  | indexedProduct label count start step ihStart ihStep =>
      exact ⟨ihStart hcontained.1, fun j => ihStep j (hcontained.2 j)⟩

/-- Interpret a sequence directly as a metadata-free unitary operator.

The multiplication order is a right fold over execution order: a later step
multiplies the accumulated operator on the left. Keeping the proof inside the
unitary-group value makes unitarity a property of the evaluator rather than a
separate stored circuit field. -/
def toUnitary : {R : Register} → UnitarySequence R → UnitaryOperator R
  | _, .id _ => 1
  | _, .leaf atom => atom.operator
  | _, .seq left right => right.toUnitary * left.toUnitary
  | _, .tensor left right =>
      UnitaryOperator.prodTensor left.toUnitary right.toUnitary
  | _, .reindex equiv body => UnitaryOperator.reindex equiv body.toUnitary
  | _, .dagger body => body.toUnitary.dagger
  | _, .controlled control activationValue body =>
      UnitaryOperator.controlled control activationValue body.toUnitary
  | _, .iterate count body => body.toUnitary ^ count
  | _, .indexedProduct _ _ start step =>
      (List.ofFn (fun j => (step j).toUnitary)).foldl
        (fun accumulated next => next * accumulated) start.toUnitary

/-- Ordered strict execution events projected from the circuit syntax.

Sequential and tensor nodes retain left-to-right construction order.  An
adjoint reverses execution order, control transforms every enclosed event,
and the two regular-product nodes expand in increasing iteration/index order.
This list is the execution witness; the unordered pool below is its literal
multiplicity projection. -/
def eventTrace : {R : Register} → UnitarySequence R →
    List (Resource.Event .quantum)
  | _, .id _ => []
  | _, .leaf atom => [atom.event]
  | _, .seq left right => left.eventTrace ++ right.eventTrace
  | _, .tensor left right => left.eventTrace ++ right.eventTrace
  | _, .reindex _ body => body.eventTrace
  | _, .dagger body => body.eventTrace.reverse
  | _, .controlled control _ body =>
      body.eventTrace.map fun event =>
        event.controlForDimension (Fintype.card control.Index)
  | _, .iterate count body =>
      (List.replicate count body.eventTrace).flatten
  | _, .indexedProduct _ _ start step =>
      start.eventTrace ++
        (List.ofFn fun j => (step j).eventTrace).flatten

/-- Strict event pool projected from the same syntax as unitary semantics.

Control maps every unitary event to the independently budgeted coordinate
derived from the finite control-register dimension. -/
def eventCost : {R : Register} → UnitarySequence R → ResourcePool .quantum
  | _, .id _ => 0
  | _, .leaf atom => ResourcePool.singleton atom.event
  | _, .seq left right => left.eventCost + right.eventCost
  | _, .tensor left right => left.eventCost + right.eventCost
  | _, .reindex _ body => body.eventCost
  | _, .dagger body => body.eventCost
  | _, .controlled control _ body =>
      ResourcePool.controlForDimension
        (Fintype.card control.Index) body.eventCost
  | _, .iterate count body => count • body.eventCost
  | _, .indexedProduct _ _ start step =>
      start.eventCost + ∑ j, (step j).eventCost

/-- Strict event critical path projected from the same syntax.

A control node remains visible in the symbolic history while every atom below
it is mapped to the independently budgeted controlled coordinate. Its tensor
branches are serialized in their existing event order because every event now
uses the same added control systems. -/
def eventDepth : {R : Register} → UnitarySequence R →
    DepthExpr (Resource.Event .quantum)
  | _, .id _ => .id
  | _, .leaf atom => .atom atom.event
  | _, .seq left right => .seq left.eventDepth right.eventDepth
  | _, .tensor left right => .tensor left.eventDepth right.eventDepth
  | _, .reindex _ body => body.eventDepth
  | _, .dagger body => .inverse body.eventDepth
  | _, .controlled control _ body =>
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) body.eventDepth)
  | _, .iterate count body => .iterate count body.eventDepth
  | _, .indexedProduct label count start step =>
      .indexedProduct label count start.eventDepth (fun j => (step j).eventDepth)

@[simp]
theorem toUnitary_id (R : Register) :
    toUnitary (.id R) = (1 : UnitaryOperator R) := rfl

@[simp]
theorem toUnitary_leaf {R : Register} (leaf : UnitaryLeaf R) :
    toUnitary (.leaf leaf) = leaf.operator := rfl

@[simp]
theorem toUnitary_seq {R : Register} (left right : UnitarySequence R) :
    toUnitary (.seq left right) = right.toUnitary * left.toUnitary := rfl

@[simp]
theorem toUnitary_reindex {R S : Register} (equiv : R.Index ≃ S.Index)
    (body : UnitarySequence R) :
    toUnitary (.reindex equiv body) = UnitaryOperator.reindex equiv body.toUnitary := rfl

/-- Coercing a right-folded unitary product gives the corresponding raw matrix
right fold. -/
theorem coe_foldl_unitary {R : Register}
    (start : UnitaryOperator R)
    (steps : List (UnitaryOperator R)) :
    ((steps.foldl (fun accumulated next => next * accumulated) start :
        UnitaryOperator R) : HilbertOperator R) =
      (List.map (fun next : UnitaryOperator R =>
        (next : HilbertOperator R)) steps).foldl
        (fun accumulated next => next * accumulated) (start : HilbertOperator R) := by
  induction steps generalizing start with
  | nil => rfl
  | cons next steps ih =>
      change (((steps.foldl (fun accumulated next => next * accumulated)
        (next * start) : UnitaryOperator R)) : HilbertOperator R) = _
      simpa using ih (next * start)

@[simp]
theorem eventCost_id (R : Register) : eventCost (.id R) = 0 := rfl

@[simp]
theorem eventCost_leaf {R : Register} (leaf : UnitaryLeaf R) :
    eventCost (.leaf leaf) = ResourcePool.singleton leaf.event := rfl

@[simp]
theorem eventCost_seq {R : Register} (left right : UnitarySequence R) :
    eventCost (.seq left right) = eventCost left + eventCost right := rfl

@[simp]
theorem eventCost_tensor {R S : Register} (left : UnitarySequence R)
    (right : UnitarySequence S) :
    eventCost (.tensor left right) = eventCost left + eventCost right := rfl

@[simp]
theorem eventCost_reindex {R S : Register} (equiv : R.Index ≃ S.Index)
    (body : UnitarySequence R) :
    eventCost (.reindex equiv body) = eventCost body := rfl

@[simp]
theorem eventCost_controlled {R : Register} (control : Register)
    (activationValue : control.Index) (body : UnitarySequence R) :
    eventCost (.controlled control activationValue body) =
      ResourcePool.controlForDimension
        (Fintype.card control.Index) (eventCost body) := rfl

@[simp]
theorem eventTrace_id (R : Register) : eventTrace (.id R) = [] := rfl

@[simp]
theorem eventTrace_leaf {R : Register} (leaf : UnitaryLeaf R) :
    eventTrace (.leaf leaf) = [leaf.event] := rfl

@[simp]
theorem eventTrace_seq {R : Register} (left right : UnitarySequence R) :
    eventTrace (.seq left right) = eventTrace left ++ eventTrace right := rfl

@[simp]
theorem eventTrace_tensor {R S : Register} (left : UnitarySequence R)
    (right : UnitarySequence S) :
    eventTrace (.tensor left right) = eventTrace left ++ eventTrace right := rfl

@[simp]
theorem eventTrace_reindex {R S : Register} (equiv : R.Index ≃ S.Index)
    (body : UnitarySequence R) :
    eventTrace (.reindex equiv body) = eventTrace body := rfl

@[simp]
theorem eventTrace_dagger {R : Register} (body : UnitarySequence R) :
    eventTrace (.dagger body) = (eventTrace body).reverse := rfl

@[simp]
theorem eventTrace_controlled {R : Register} (control : Register)
    (activationValue : control.Index) (body : UnitarySequence R) :
    eventTrace (.controlled control activationValue body) =
      body.eventTrace.map fun event =>
        event.controlForDimension (Fintype.card control.Index) := rfl

@[simp]
theorem eventTrace_iterate {R : Register} (count : Nat)
    (body : UnitarySequence R) :
    eventTrace (.iterate count body) =
      (List.replicate count body.eventTrace).flatten := rfl

@[simp]
theorem eventTrace_indexedProduct {R : Register} (label : String)
    (count : Nat) (start : UnitarySequence R)
    (step : Fin count → UnitarySequence R) :
    eventTrace (.indexedProduct label count start step) =
      start.eventTrace ++
        (List.ofFn fun j => (step j).eventTrace).flatten := rfl

@[simp]
theorem eventDepth_id (R : Register) : eventDepth (.id R) = .id := rfl

@[simp]
theorem eventDepth_leaf {R : Register} (leaf : UnitaryLeaf R) :
    eventDepth (.leaf leaf) = .atom leaf.event := rfl

@[simp]
theorem eventDepth_seq {R : Register} (left right : UnitarySequence R) :
    eventDepth (.seq left right) =
      .seq (eventDepth left) (eventDepth right) := rfl

@[simp]
theorem eventDepth_tensor {R S : Register} (left : UnitarySequence R)
    (right : UnitarySequence S) :
    eventDepth (.tensor left right) =
      .tensor (eventDepth left) (eventDepth right) := rfl

@[simp]
theorem eventDepth_reindex {R S : Register} (equiv : R.Index ≃ S.Index)
    (body : UnitarySequence R) :
    eventDepth (.reindex equiv body) = eventDepth body := rfl

@[simp]
theorem eventDepth_dagger {R : Register} (body : UnitarySequence R) :
    eventDepth (.dagger body) = .inverse (eventDepth body) := rfl

@[simp]
theorem eventDepth_controlled {R : Register} (control : Register)
    (activationValue : control.Index) (body : UnitarySequence R) :
    eventDepth (.controlled control activationValue body) =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) (eventDepth body)) := rfl

/-- Linear event accounting and symbolic event depth are two interpretations
of the same sequence tree. -/
theorem resourcesFromEventDepth_eq_eventCost {R : Register}
    (sequence : UnitarySequence R) :
    DepthExpr.costEval (fun event => ResourcePool.singleton event)
        sequence.eventDepth = sequence.eventCost := by
  induction sequence with
  | id => rfl
  | leaf atom => rfl
  | seq left right leftIH rightIH =>
      simp [eventDepth, eventCost, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      simp [eventDepth, eventCost, leftIH, rightIH]
  | reindex equiv body bodyIH => simpa [eventDepth, eventCost] using bodyIH
  | dagger body bodyIH => simpa [eventDepth, eventCost] using bodyIH
  | controlled control activationValue body bodyIH =>
      simp only [eventDepth, eventCost, DepthExpr.costEval_controlled]
      rw [DepthExpr.resourcesFromControlEventsForDimension]
      exact congrArg
        (ResourcePool.controlForDimension (Fintype.card control.Index))
        bodyIH
  | iterate count body bodyIH => simp [eventDepth, eventCost, bodyIH]
  | indexedProduct label count start step startIH stepIH =>
      simp [eventDepth, eventCost, startIH, stepIH]

private theorem ofList_flatten_eventTraces
    (traces : List (List (Resource.Event .quantum))) :
    ResourcePool.ofList traces.flatten =
      (traces.map ResourcePool.ofList).sum := by
  induction traces with
  | nil => rfl
  | cons trace traces ih =>
      simp [ih]

/-- Forgetting event order from the syntax-derived trace gives exactly the
syntax-derived strict event pool. -/
@[simp] theorem ofList_eventTrace_eq_eventCost {R : Register}
    (sequence : UnitarySequence R) :
    ResourcePool.ofList sequence.eventTrace = sequence.eventCost := by
  induction sequence with
  | id => rfl
  | leaf atom => rfl
  | seq left right leftIH rightIH =>
      simp [eventTrace, eventCost, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      simp [eventTrace, eventCost, leftIH, rightIH]
  | reindex equiv body bodyIH => simpa [eventTrace, eventCost] using bodyIH
  | dagger body bodyIH =>
      simpa [eventTrace, eventCost, ResourcePool.ofList] using bodyIH
  | controlled control activationValue body bodyIH =>
      change ResourcePool.ofList
          (body.eventTrace.map fun event =>
            event.controlForDimension (Fintype.card control.Index)) =
        ResourcePool.controlForDimension
          (Fintype.card control.Index) body.eventCost
      rw [← bodyIH]
      rfl
  | iterate count body bodyIH =>
      rw [eventTrace, eventCost, ofList_flatten_eventTraces]
      simp [bodyIH]
  | indexedProduct label count start step startIH stepIH =>
      rw [eventTrace, eventCost, ResourcePool.ofList_append,
        ofList_flatten_eventTraces]
      simp [startIH, stepIH, List.map_ofFn, List.sum_ofFn,
        Function.comp_def]

end

end UnitarySequence

end QuantumAlg

end
