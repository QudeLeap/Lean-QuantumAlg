/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Canonical quantum-control accounting

Quantum control is a pure transformation of gate and opaque-subroutine event
coordinates.  A subroutine is declared once by its base `SubroutineLabel`;
each control layer appends its register dimension to a canonical inner-to-outer
list.  Consequently every controlled form is an independent strict resource
coordinate.

The same transformation acts pointwise on `ResourcePool` and on the atoms of a
`DepthExpr`. A nonempty added control also serializes tensor branches: every
event now uses the same control systems. The existing left-to-right event
order supplies that schedule. An empty control list preserves the original
parallel structure. Durations remain independently assigned to native events.
-/

section

namespace QuantumAlg

open scoped BigOperators

namespace Resource.GateLabel

/-- Append several control-register dimensions, ordered from inner to outer. -/
def controlForDimensions (label : GateLabel)
    (dimensions : List Nat) : GateLabel :=
  { label with controlDimensions := label.controlDimensions ++ dimensions }

/-- Append one outer control-register dimension to a gate coordinate. -/
def controlForDimension (label : GateLabel) (dimension : Nat) : GateLabel :=
  label.controlForDimensions [dimension]

@[simp] theorem controlForDimensions_nil (label : GateLabel) :
    label.controlForDimensions [] = label := by
  cases label
  simp [controlForDimensions]

@[simp] theorem controlForDimensions_append (label : GateLabel)
    (inner outer : List Nat) :
    (label.controlForDimensions inner).controlForDimensions outer =
      label.controlForDimensions (inner ++ outer) := by
  cases label
  simp [controlForDimensions, List.append_assoc]

@[simp] theorem controlForDimension_controlForDimension (label : GateLabel)
    (inner outer : Nat) :
    (label.controlForDimension inner).controlForDimension outer =
      label.controlForDimensions [inner, outer] := by
  simp [controlForDimension]

theorem controlForDimensions_injective (dimensions : List Nat) :
    Function.Injective (fun label : GateLabel =>
      label.controlForDimensions dimensions) := by
  rintro ⟨leftFamily, leftName, leftParameters, leftControls⟩
    ⟨rightFamily, rightName, rightParameters, rightControls⟩ equality
  simpa [controlForDimensions] using equality

theorem controlForDimension_injective (dimension : Nat) :
    Function.Injective (fun label : GateLabel =>
      label.controlForDimension dimension) :=
  controlForDimensions_injective [dimension]

end Resource.GateLabel

namespace Resource.QuantumSubroutineLabel

/-- Append several control-register dimensions, ordered from inner to outer. -/
def controlForDimensions (label : QuantumSubroutineLabel)
    (dimensions : List Nat) : QuantumSubroutineLabel :=
  { label with controlDimensions := label.controlDimensions ++ dimensions }

/-- Append one outer control-register dimension to an opaque quantum
subroutine coordinate. -/
def controlForDimension (label : QuantumSubroutineLabel)
    (dimension : Nat) : QuantumSubroutineLabel :=
  label.controlForDimensions [dimension]

@[simp] theorem controlForDimensions_nil (label : QuantumSubroutineLabel) :
    label.controlForDimensions [] = label := by
  cases label
  simp [controlForDimensions]

@[simp] theorem controlForDimensions_append (label : QuantumSubroutineLabel)
    (inner outer : List Nat) :
    (label.controlForDimensions inner).controlForDimensions outer =
      label.controlForDimensions (inner ++ outer) := by
  cases label
  simp [controlForDimensions, List.append_assoc]

@[simp] theorem controlForDimension_controlForDimension
    (label : QuantumSubroutineLabel) (inner outer : Nat) :
    (label.controlForDimension inner).controlForDimension outer =
      label.controlForDimensions [inner, outer] := by
  simp [controlForDimension]

@[simp] theorem quantum_controlForDimensions (base : SubroutineLabel)
    (dimensions : List Nat) :
    base.quantum.controlForDimensions dimensions =
      { base := base, controlDimensions := dimensions } := by
  simp [controlForDimensions]

@[simp] theorem quantum_controlForDimension (base : SubroutineLabel)
    (dimension : Nat) :
    base.quantum.controlForDimension dimension =
      { base := base, controlDimensions := [dimension] } := by
  simp [controlForDimension]

theorem controlForDimensions_injective (dimensions : List Nat) :
    Function.Injective (fun label : QuantumSubroutineLabel =>
      label.controlForDimensions dimensions) := by
  rintro ⟨leftBase, leftControls⟩ ⟨rightBase, rightControls⟩ equality
  simpa [controlForDimensions] using equality

theorem controlForDimension_injective (dimension : Nat) :
    Function.Injective (fun label : QuantumSubroutineLabel =>
      label.controlForDimension dimension) :=
  controlForDimensions_injective [dimension]

/-- Adding a control layer always creates a distinct quantum capability. -/
theorem controlForDimension_ne (label : QuantumSubroutineLabel)
    (dimension : Nat) :
    label.controlForDimension dimension ≠ label := by
  intro equality
  have lengths := congrArg
    (fun current : QuantumSubroutineLabel =>
      current.controlDimensions.length) equality
  simp [controlForDimension, controlForDimensions] at lengths

/-- Two singly controlled forms of the same label collide only when their
control-register dimensions agree. -/
theorem controlForDimension_injective_dimension
    (label : QuantumSubroutineLabel) :
    Function.Injective label.controlForDimension := by
  intro left right equality
  have controls := congrArg QuantumSubroutineLabel.controlDimensions equality
  change label.controlDimensions ++ [left] =
    label.controlDimensions ++ [right] at controls
  have singletonEquality := List.append_cancel_left controls
  injection singletonEquality

end Resource.QuantumSubroutineLabel

namespace Resource.Event

/-- Transform the unitary event coordinates for several nested controls.

Gate and opaque-subroutine coordinates accumulate the supplied dimensions.
Other event constructors are unchanged: the circuit control layer only applies
this map to unitary circuit atoms, while keeping the total event function
available for ledger and depth-expression traversal.
-/
def controlForDimensions (event : Event .quantum)
    (dimensions : List Nat) : Event .quantum :=
  match event with
  | .classicalOperation label => .classicalOperation label
  | .classicalSubroutine label => .classicalSubroutine label
  | .gate label => .gate (label.controlForDimensions dimensions)
  | .preparation label => .preparation label
  | .measurement label => .measurement label
  | .quantumSubroutine label =>
      .quantumSubroutine (label.controlForDimensions dimensions)

/-- Transform a unitary event coordinate for one outer control layer. -/
public def controlForDimension (event : Event .quantum)
    (dimension : Nat) : Event .quantum :=
  event.controlForDimensions [dimension]

@[simp] theorem controlForDimensions_nil (event : Event .quantum) :
    event.controlForDimensions [] = event := by
  cases event <;> simp [controlForDimensions]

@[simp] theorem controlForDimensions_append (event : Event .quantum)
    (inner outer : List Nat) :
    (event.controlForDimensions inner).controlForDimensions outer =
      event.controlForDimensions (inner ++ outer) := by
  cases event <;> simp [controlForDimensions]

@[simp] theorem controlForDimension_controlForDimension
    (event : Event .quantum) (inner outer : Nat) :
    (event.controlForDimension inner).controlForDimension outer =
      event.controlForDimensions [inner, outer] := by
  simp [controlForDimension]

@[simp] theorem controlForDimensions_gate (label : GateLabel)
    (dimensions : List Nat) :
    (Event.gate label).controlForDimensions dimensions =
      .gate (label.controlForDimensions dimensions) :=
  rfl

@[simp] theorem controlForDimension_gate (label : GateLabel)
    (dimension : Nat) :
    (Event.gate label).controlForDimension dimension =
      .gate (label.controlForDimension dimension) :=
  rfl

@[simp] theorem controlForDimensions_quantumSubroutine
    (label : QuantumSubroutineLabel) (dimensions : List Nat) :
    (Event.quantumSubroutine label).controlForDimensions dimensions =
      .quantumSubroutine (label.controlForDimensions dimensions) :=
  rfl

@[simp] theorem controlForDimension_quantumSubroutine
    (label : QuantumSubroutineLabel) (dimension : Nat) :
    (Event.quantumSubroutine label).controlForDimension dimension =
      .quantumSubroutine (label.controlForDimension dimension) :=
  rfl

theorem controlForDimensions_injective (dimensions : List Nat) :
    Function.Injective (fun event : Event .quantum =>
      event.controlForDimensions dimensions) := by
  intro left right equality
  cases left <;> cases right <;>
    simp_all [controlForDimensions,
      (GateLabel.controlForDimensions_injective dimensions).eq_iff,
      (QuantumSubroutineLabel.controlForDimensions_injective dimensions).eq_iff]

theorem controlForDimension_injective (dimension : Nat) :
    Function.Injective (fun event : Event .quantum =>
      event.controlForDimension dimension) :=
  controlForDimensions_injective [dimension]

/-- An uncontrolled opaque-subroutine event differs from every singly
controlled form of the same base declaration. -/
theorem quantumSubroutine_controlForDimension_ne
    (base : SubroutineLabel) (dimension : Nat) :
    (Event.quantumSubroutine base.quantum).controlForDimension dimension ≠
      .quantumSubroutine base.quantum := by
  intro equality
  apply QuantumSubroutineLabel.controlForDimension_ne base.quantum dimension
  injection equality

end Resource.Event

namespace ResourcePool

/-- Apply a normalized nested-control transform to every event coordinate. -/
def controlForDimensions (dimensions : List Nat)
    (pool : ResourcePool .quantum) : ResourcePool .quantum :=
  pool.map (fun event => event.controlForDimensions dimensions)

/-- Apply one outer control layer to every event coordinate. -/
def controlForDimension (dimension : Nat)
    (pool : ResourcePool .quantum) : ResourcePool .quantum :=
  controlForDimensions [dimension] pool

@[simp] theorem controlForDimensions_nil (pool : ResourcePool .quantum) :
    controlForDimensions [] pool = pool := by
  simp [controlForDimensions]

@[simp] theorem controlForDimensions_append (inner outer : List Nat)
    (pool : ResourcePool .quantum) :
    controlForDimensions outer (controlForDimensions inner pool) =
      controlForDimensions (inner ++ outer) pool := by
  simp [controlForDimensions, Multiset.map_map]

@[simp] theorem controlForDimension_controlForDimension (inner outer : Nat)
    (pool : ResourcePool .quantum) :
    controlForDimension outer (controlForDimension inner pool) =
      controlForDimensions [inner, outer] pool := by
  simp [controlForDimension]

@[simp] theorem controlForDimensions_zero (dimensions : List Nat) :
    controlForDimensions dimensions (0 : ResourcePool .quantum) = 0 :=
  rfl

@[simp] theorem controlForDimensions_add (dimensions : List Nat)
    (left right : ResourcePool .quantum) :
    controlForDimensions dimensions (left + right) =
      controlForDimensions dimensions left +
        controlForDimensions dimensions right := by
  simp [controlForDimensions]

@[simp] theorem controlForDimensions_nsmul (dimensions : List Nat)
    (multiplicity : Nat) (pool : ResourcePool .quantum) :
    controlForDimensions dimensions (multiplicity • pool) =
      multiplicity • controlForDimensions dimensions pool := by
  simpa [controlForDimensions] using Multiset.map_nsmul
    (fun event : Resource.Event .quantum =>
      event.controlForDimensions dimensions) multiplicity pool

@[simp] theorem controlForDimensions_scale (dimensions : List Nat)
    (multiplicity : Nat) (pool : ResourcePool .quantum) :
    controlForDimensions dimensions (scale multiplicity pool) =
      scale multiplicity (controlForDimensions dimensions pool) := by
  simp [scale]

private theorem controlForDimensions_finset_sum (dimensions : List Nat)
    {ι : Type} (indices : Finset ι)
    (pool : ι → ResourcePool .quantum) :
    controlForDimensions dimensions (∑ index ∈ indices, pool index) =
      ∑ index ∈ indices, controlForDimensions dimensions (pool index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices fresh inductionHypothesis =>
      simp [fresh, inductionHypothesis]

@[simp] theorem controlForDimensions_sum (dimensions : List Nat)
    {ι : Type} [Fintype ι] (pool : ι → ResourcePool .quantum) :
    controlForDimensions dimensions (∑ index, pool index) =
      ∑ index, controlForDimensions dimensions (pool index) := by
  simpa using controlForDimensions_finset_sum dimensions Finset.univ pool

@[simp] theorem controlForDimensions_singleton (dimensions : List Nat)
    (event : Resource.Event .quantum) (multiplicity : Nat) :
    controlForDimensions dimensions (singleton event multiplicity) =
      singleton (event.controlForDimensions dimensions) multiplicity := by
  simp [controlForDimensions, singleton]

@[simp] theorem controlForDimension_zero (dimension : Nat) :
    controlForDimension dimension (0 : ResourcePool .quantum) = 0 :=
  rfl

@[simp] theorem controlForDimension_add (dimension : Nat)
    (left right : ResourcePool .quantum) :
    controlForDimension dimension (left + right) =
      controlForDimension dimension left + controlForDimension dimension right := by
  simp [controlForDimension]

@[simp] theorem controlForDimension_singleton (dimension : Nat)
    (event : Resource.Event .quantum) (multiplicity : Nat) :
    controlForDimension dimension (singleton event multiplicity) =
      singleton (event.controlForDimension dimension) multiplicity := by
  simpa only [controlForDimension, Resource.Event.controlForDimension] using
    controlForDimensions_singleton [dimension] event multiplicity

/-- Pointwise control preserves the exact multiplicity of each source
coordinate. -/
@[simp] theorem count_controlForDimensions (dimensions : List Nat)
    (event : Resource.Event .quantum) (pool : ResourcePool .quantum) :
    count (event.controlForDimensions dimensions)
        (controlForDimensions dimensions pool) =
      count event pool := by
  unfold count
  rw [controlForDimensions, Multiset.count_map]
  simpa [(Resource.Event.controlForDimensions_injective dimensions).eq_iff] using
    (Multiset.count_eq_card_filter_eq pool event).symm

@[simp] theorem count_controlForDimension (dimension : Nat)
    (event : Resource.Event .quantum) (pool : ResourcePool .quantum) :
    count (event.controlForDimension dimension)
        (controlForDimension dimension pool) =
      count event pool :=
  count_controlForDimensions [dimension] event pool

/-- Pointwise control is an order embedding: it changes coordinates but never
pools or drops them. -/
@[simp] theorem controlForDimensions_le_controlForDimensions_iff
    (dimensions : List Nat) {left right : ResourcePool .quantum} :
    controlForDimensions dimensions left ≤ controlForDimensions dimensions right ↔
      left ≤ right := by
  exact Multiset.map_le_map_iff
    (Resource.Event.controlForDimensions_injective dimensions)

@[simp] theorem controlForDimension_le_controlForDimension_iff
    (dimension : Nat) {left right : ResourcePool .quantum} :
    controlForDimension dimension left ≤ controlForDimension dimension right ↔
      left ≤ right :=
  controlForDimensions_le_controlForDimensions_iff [dimension]

private theorem not_singleton_le_singleton_of_ne
    {left right : Resource.Event .quantum} (different : left ≠ right) :
    ¬singleton left ≤ singleton right := by
  apply not_le_of_count_gt left
  simp [count_singleton_of_ne different]

/-- A base-subroutine budget does not pay for its singly controlled form. -/
theorem not_controlledSubroutine_le_baseSubroutine
    (base : Resource.SubroutineLabel) (dimension : Nat) :
    ¬singleton
        (Resource.Event.controlForDimension
          (.quantumSubroutine base.quantum) dimension) ≤
      singleton (.quantumSubroutine base.quantum) := by
  apply not_singleton_le_singleton_of_ne
  exact Resource.Event.quantumSubroutine_controlForDimension_ne base dimension

/-- A singly controlled budget does not pay for the corresponding base
subroutine either. -/
theorem not_baseSubroutine_le_controlledSubroutine
    (base : Resource.SubroutineLabel) (dimension : Nat) :
    ¬singleton (.quantumSubroutine base.quantum) ≤
      singleton
        (Resource.Event.controlForDimension
          (.quantumSubroutine base.quantum) dimension) := by
  apply not_singleton_le_singleton_of_ne
  exact (Resource.Event.quantumSubroutine_controlForDimension_ne
    base dimension).symm

end ResourcePool

namespace DepthExpr

/-- Add the normalized control dimensions to every event and serialize shared-control work.
Only the empty control list preserves tensor parallelism. -/
def controlEventsForDimensions (dimensions : List Nat) :
    DepthExpr (Resource.Event .quantum) →
      DepthExpr (Resource.Event .quantum)
  | .id => .id
  | .atom event => .atom (event.controlForDimensions dimensions)
  | .seq left right =>
      .seq (controlEventsForDimensions dimensions left)
        (controlEventsForDimensions dimensions right)
  | .tensor left right =>
      match dimensions with
      | [] => .tensor (controlEventsForDimensions [] left)
          (controlEventsForDimensions [] right)
      | dimension :: rest =>
          .seq (controlEventsForDimensions (dimension :: rest) left)
            (controlEventsForDimensions (dimension :: rest) right)
  | .inverse body => .inverse (controlEventsForDimensions dimensions body)
  | .controlled label body =>
      .controlled label (controlEventsForDimensions dimensions body)
  | .iterate count body =>
      .iterate count (controlEventsForDimensions dimensions body)
  | .indexedProduct label count start step =>
      .indexedProduct label count (controlEventsForDimensions dimensions start)
        fun j => controlEventsForDimensions dimensions (step j)

/-- Add one shared outer control and serialize its actual event schedule. -/
def controlEventsForDimension (dimension : Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    DepthExpr (Resource.Event .quantum) :=
  controlEventsForDimensions [dimension] expression

@[simp] theorem controlEventsForDimensions_nil
    (expression : DepthExpr (Resource.Event .quantum)) :
    controlEventsForDimensions [] expression = expression := by
  induction expression with
  | id => rfl
  | atom event => simp [controlEventsForDimensions]
  | seq left right leftIH rightIH =>
      simp [controlEventsForDimensions, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      simp [controlEventsForDimensions, leftIH, rightIH]
  | inverse body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | controlled label body bodyIH =>
      simp [controlEventsForDimensions, bodyIH]
  | iterate count body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | indexedProduct label count start step startIH stepIH =>
      simp [controlEventsForDimensions, startIH, stepIH]

@[simp] theorem controlEventsForDimensions_append (inner outer : List Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    controlEventsForDimensions outer
        (controlEventsForDimensions inner expression) =
      controlEventsForDimensions (inner ++ outer) expression := by
  induction expression with
  | id => rfl
  | atom event => simp [controlEventsForDimensions]
  | seq left right leftIH rightIH =>
      simp [controlEventsForDimensions, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      cases inner <;> cases outer <;>
        simp [controlEventsForDimensions, leftIH, rightIH]
  | inverse body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | controlled label body bodyIH =>
      simp [controlEventsForDimensions, bodyIH]
  | iterate count body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | indexedProduct label count start step startIH stepIH =>
      simp [controlEventsForDimensions, startIH, stepIH]

@[simp] theorem controlEventsForDimension_controlEventsForDimension
    (inner outer : Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    controlEventsForDimension outer
        (controlEventsForDimension inner expression) =
      controlEventsForDimensions [inner, outer] expression := by
  simp [controlEventsForDimension]

/-- Linear cost evaluation commutes with the event-control transform. -/
theorem costEval_controlEventsForDimensions {M : Type} [AddCommMonoid M]
    (assign : Resource.Event .quantum → M) (dimensions : List Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    costEval assign (controlEventsForDimensions dimensions expression) =
      costEval (fun event => assign (event.controlForDimensions dimensions))
        expression := by
  induction expression with
  | id => rfl
  | atom event => rfl
  | seq left right leftIH rightIH =>
      simp [controlEventsForDimensions, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      cases dimensions <;> simp [controlEventsForDimensions, leftIH, rightIH]
  | inverse body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | controlled label body bodyIH =>
      simp [controlEventsForDimensions, bodyIH]
  | iterate count body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | indexedProduct label count start step startIH stepIH =>
      simp [controlEventsForDimensions, startIH, stepIH]

theorem costEval_controlEventsForDimension {M : Type} [AddCommMonoid M]
    (assign : Resource.Event .quantum → M) (dimension : Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    costEval assign (controlEventsForDimension dimension expression) =
      costEval (fun event => assign (event.controlForDimension dimension))
        expression :=
  costEval_controlEventsForDimensions assign [dimension] expression

/-- Nonempty shared controls give an additive schedule; no added control retains original depth. -/
theorem depthEval_controlEventsForDimensions
    (assign : Resource.Event .quantum → Nat) (dimensions : List Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    depthEval assign (controlEventsForDimensions dimensions expression) =
      if dimensions = [] then depthEval assign expression
      else costEval (fun event => assign (event.controlForDimensions dimensions)) expression := by
  cases dimensions with
  | nil => simp
  | cons dimension rest =>
      change depthEval assign (controlEventsForDimensions (dimension :: rest) expression) =
        costEval (fun event => assign (event.controlForDimensions (dimension :: rest))) expression
      induction expression with
      | id => rfl
      | atom event => rfl
      | seq left right leftIH rightIH =>
          simp [controlEventsForDimensions, leftIH, rightIH]
      | tensor left right leftIH rightIH =>
          simp [controlEventsForDimensions, leftIH, rightIH]
      | inverse body bodyIH => simp [controlEventsForDimensions, bodyIH]
      | controlled label body bodyIH =>
          simp [controlEventsForDimensions, bodyIH]
      | iterate count body bodyIH =>
          simp [controlEventsForDimensions, bodyIH]
      | indexedProduct label count start step startIH stepIH =>
          simp [controlEventsForDimensions, startIH, stepIH]

theorem depthEval_controlEventsForDimension
    (assign : Resource.Event .quantum → Nat) (dimension : Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    depthEval assign (controlEventsForDimension dimension expression) =
      costEval (fun event => assign (event.controlForDimension dimension)) expression := by
  simpa only [controlEventsForDimension, Resource.Event.controlForDimension,
    List.cons_ne_nil, if_false] using
    depthEval_controlEventsForDimensions assign [dimension] expression

/-- A shared control makes every matching event sequential at its transformed focus coordinate. -/
@[simp] theorem queryDepthEval_controlEventsForDimensions
    (focus : Resource.Event .quantum) (dimensions : List Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    queryDepthEval (focus.controlForDimensions dimensions)
        (controlEventsForDimensions dimensions expression) =
      if dimensions = [] then queryDepthEval focus expression
      else costEval (indicator focus) expression := by
  by_cases noControls : dimensions = []
  · subst dimensions
    simp
  · simp only [queryDepthEval, depthEval_controlEventsForDimensions, noControls, if_false]
    congr 1
    funext event
    simp [indicator,
      (Resource.Event.controlForDimensions_injective dimensions).eq_iff]

@[simp] theorem queryDepthEval_controlEventsForDimension
    (focus : Resource.Event .quantum) (dimension : Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    queryDepthEval (focus.controlForDimension dimension)
        (controlEventsForDimension dimension expression) =
      costEval (indicator focus) expression := by
  simpa only [controlEventsForDimension, Resource.Event.controlForDimension,
    List.cons_ne_nil, if_false] using
    queryDepthEval_controlEventsForDimensions focus [dimension] expression

/-- Linearizing a control-transformed event-depth tree is exactly the
pointwise control transform of its strict event pool. -/
theorem resourcesFromControlEventsForDimensions (dimensions : List Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    costEval (fun event => ResourcePool.singleton event)
        (controlEventsForDimensions dimensions expression) =
      ResourcePool.controlForDimensions dimensions
        (costEval (fun event => ResourcePool.singleton event) expression) := by
  induction expression with
  | id => rfl
  | atom event => simp [controlEventsForDimensions]
  | seq left right leftIH rightIH =>
      simp [controlEventsForDimensions, leftIH, rightIH]
  | tensor left right leftIH rightIH =>
      cases dimensions <;> simp [controlEventsForDimensions, leftIH, rightIH]
  | inverse body bodyIH => simp [controlEventsForDimensions, bodyIH]
  | controlled label body bodyIH =>
      simp [controlEventsForDimensions, bodyIH]
  | iterate count body bodyIH =>
      simp [controlEventsForDimensions, bodyIH]
  | indexedProduct label count start step startIH stepIH =>
      simp [controlEventsForDimensions, startIH, stepIH]

theorem resourcesFromControlEventsForDimension (dimension : Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    costEval (fun event => ResourcePool.singleton event)
        (controlEventsForDimension dimension expression) =
      ResourcePool.controlForDimension dimension
        (costEval (fun event => ResourcePool.singleton event) expression) :=
  resourcesFromControlEventsForDimensions [dimension] expression

/-- The max-plus depth of a control-transformed event tree remains bounded by
its linear cost under the same transformed coordinate weights. -/
theorem depthEval_controlEventsForDimensions_le_costEval
    (assign : Resource.Event .quantum → Nat) (dimensions : List Nat)
    (expression : DepthExpr (Resource.Event .quantum)) :
    depthEval assign (controlEventsForDimensions dimensions expression) ≤
      costEval assign (controlEventsForDimensions dimensions expression) :=
  depthEval_le_costEval assign _

namespace ControlAccountingFixtures

private def base : Resource.SubroutineLabel :=
  { family := "fixture", name := "opaque-access", parameters := [8] }

private def baseEvent : Resource.Event .quantum :=
  .quantumSubroutine base.quantum

private def controlledEvent : Resource.Event .quantum :=
  baseEvent.controlForDimension 2

private def nestedEvent : Resource.Event .quantum :=
  (baseEvent.controlForDimension 2).controlForDimension 4

/-- Base, singly controlled, and nested coordinates are pairwise distinct. -/
example : baseEvent ≠ controlledEvent ∧ controlledEvent ≠ nestedEvent ∧
    baseEvent ≠ nestedEvent := by
  decide

/-- Nested controls normalize to one inner-to-outer dimension list. -/
example : nestedEvent = baseEvent.controlForDimensions [2, 4] := by
  decide

/-- The base focus does not count a controlled atom. -/
example : queryDepthEval baseEvent (.atom controlledEvent) = 0 := by
  decide

/-- The derived focus counts exactly the controlled atom. -/
example : queryDepthEval controlledEvent (.atom controlledEvent) = 1 := by
  decide

/-- A base budget cannot pay for its controlled coordinate. -/
example : ¬ResourcePool.singleton controlledEvent ≤
    ResourcePool.singleton baseEvent := by
  exact ResourcePool.not_controlledSubroutine_le_baseSubroutine base 2

/-- A controlled budget cannot pay for its base coordinate. -/
example : ¬ResourcePool.singleton baseEvent ≤
    ResourcePool.singleton controlledEvent := by
  exact ResourcePool.not_baseSubroutine_le_controlledSubroutine base 2

end ControlAccountingFixtures

end DepthExpr

end QuantumAlg

end
