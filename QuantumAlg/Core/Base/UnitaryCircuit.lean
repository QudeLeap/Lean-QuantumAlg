/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.Kind
public import QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
public import QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Pure

/-!
# Typed circuit semantics

`UnitaryCircuit R` is constructed only through the safe smart constructors owned by
`UnitaryCircuit.Construction`. This facade derives its unitary matrix, ordered strict
event trace, event pool, and symbolic event depth from the stored typed
sequence. Resource claims use these strict event projections directly.

Sequence order is execution order. Thus `seq left right` executes `left` first
and `right` second, and its matrix is `right.matrix * left.matrix`. Repetition
and indexed products remain symbolic nodes, so large regular circuits need not
be expanded into gate lists.
-/

section

namespace QuantumAlg

open scoped BigOperators

namespace UnitaryCircuit

noncomputable section

/-- Metadata-free unitary semantics derived from the circuit sequence. -/
public def matrix {R : Register} (circuit : UnitaryCircuit R) : UnitaryOperator R :=
  circuit.sequence.toUnitary

instance {R : Register} : Coe (UnitaryCircuit R) (UnitaryOperator R) :=
  ⟨matrix⟩

instance {R : Register} : CoeTail (UnitaryCircuit R) (HilbertOperator R) :=
  ⟨fun circuit => circuit.matrix⟩

instance {R : Register} : CoeOut (UnitaryCircuit R) (HilbertOperator R) :=
  ⟨fun circuit => circuit.matrix⟩

instance {R : Register} : CoeFun (UnitaryCircuit R) (fun _ => R.Index → R.Index → ℂ) :=
  ⟨fun circuit => circuit.matrix⟩

instance {R : Register} : HMul (UnitaryCircuit R) (HilbertOperator R) (HilbertOperator R) where
  hMul circuit operator := (circuit : HilbertOperator R) * operator

instance {R : Register} : HMul (HilbertOperator R) (UnitaryCircuit R) (HilbertOperator R) where
  hMul operator circuit := operator * (circuit : HilbertOperator R)

/-- Ordered strict execution events derived from the circuit sequence. -/
def eventTrace {R : Register} (circuit : UnitaryCircuit R) :
    List (Resource.Event .quantum) :=
  circuit.sequence.eventTrace

/-- Strict event pool derived from the circuit sequence. -/
public def eventCost {R : Register} (circuit : UnitaryCircuit R) : ResourcePool .quantum :=
  circuit.sequence.eventCost

/-- Strict symbolic event critical path derived from the same sequence. -/
public def eventDepth {R : Register} (circuit : UnitaryCircuit R) :
    DepthExpr (Resource.Event .quantum) :=
  circuit.sequence.eventDepth

/-- Evaluate the strict event critical path. -/
public def evaluatedEventDepth {R : Register}
    (assign : Resource.Event .quantum → Nat) (circuit : UnitaryCircuit R) : Nat :=
  DepthExpr.depthEval assign circuit.eventDepth

/-- Literal query depth of one strict event coordinate.  Unlike the legacy
query view, this performs no pooling or relabeling. -/
def eventQueryDepth {R : Register} (focus : Resource.Event .quantum)
    (circuit : UnitaryCircuit R) : Nat :=
  DepthExpr.queryDepthEval focus circuit.eventDepth















/-- Linearize the strict event-depth tree. -/
def resourcesFromEventDepth {R : Register} (circuit : UnitaryCircuit R) :
    ResourcePool .quantum :=
  DepthExpr.costEval (fun event => ResourcePool.singleton event) circuit.eventDepth

@[simp] theorem resourcesFromEventDepth_eq_eventCost {R : Register}
    (circuit : UnitaryCircuit R) :
    circuit.resourcesFromEventDepth = circuit.eventCost :=
  UnitarySequence.resourcesFromEventDepth_eq_eventCost circuit.sequence

/-- Forgetting the order of the circuit's derived execution trace gives its
strict event pool exactly. -/
@[simp] theorem ofList_eventTrace_eq_eventCost {R : Register}
    (circuit : UnitaryCircuit R) :
    ResourcePool.ofList circuit.eventTrace = circuit.eventCost :=
  UnitarySequence.ofList_eventTrace_eq_eventCost circuit.sequence

/-- Apply the derived circuit matrix to a raw state vector. -/
def applyVec {R : Register} (circuit : UnitaryCircuit R)
    (state : HilbertVector R) : HilbertVector R :=
  circuit.matrix.applyVec state

@[simp]
theorem applyVec_add {R : Register} (circuit : UnitaryCircuit R)
    (left right : HilbertVector R) :
    circuit.applyVec (left + right) = circuit.applyVec left + circuit.applyVec right :=
  HilbertOperator.applyVec_add (circuit : HilbertOperator R) left right

@[simp]
theorem applyVec_smul {R : Register} (circuit : UnitaryCircuit R) (scalar : ℂ)
    (state : HilbertVector R) :
    circuit.applyVec (scalar • state) = scalar • circuit.applyVec state :=
  HilbertOperator.applyVec_smul (circuit : HilbertOperator R) scalar state

/-- Apply the circuit semantics while preserving mathematical normalization. -/
public def applyNormalized {R : Register} (circuit : UnitaryCircuit R)
    (state : NormalizedVector R) : NormalizedVector R :=
  circuit.matrix.apply state

@[simp]
theorem applyNormalized_coe {R : Register} (circuit : UnitaryCircuit R)
    (state : NormalizedVector R) :
    ((circuit.applyNormalized state : NormalizedVector R) : HilbertVector R) =
      circuit.applyVec (state : HilbertVector R) := rfl

@[simp]
theorem applyVec_identity (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup)
    (state : HilbertVector R) :
    applyVec (identity R physical_idx physical_idx_nodup) state = state := by
  change HilbertOperator.applyVec (1 : HilbertOperator R) state = state
  exact HilbertOperator.one_applyVec state

@[simp]
theorem applyNormalized_identity (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup)
    (state : NormalizedVector R) :
    applyNormalized (identity R physical_idx physical_idx_nodup) state = state := by
  apply NormalizedVector.ext
  intro index
  exact congrArg (fun output : HilbertVector R => output index)
    (applyVec_identity R physical_idx physical_idx_nodup
      (state : HilbertVector R))

@[simp]
theorem applyVec_seq {R : Register} (left right : UnitaryCircuit R)
    (state : HilbertVector R) :
    applyVec (seq left right) state = applyVec right (applyVec left state) := by
  change HilbertOperator.applyVec
      ((right.matrix : HilbertOperator R) * (left.matrix : HilbertOperator R)) state =
    HilbertOperator.applyVec (right.matrix : HilbertOperator R)
      (HilbertOperator.applyVec (left.matrix : HilbertOperator R) state)
  exact HilbertOperator.mul_applyVec _ _ _

@[simp]
theorem applyNormalized_seq {R : Register} (left right : UnitaryCircuit R)
    (state : NormalizedVector R) :
    applyNormalized (seq left right) state =
      applyNormalized right (applyNormalized left state) := by
  apply NormalizedVector.ext
  intro i
  exact congrArg (fun ψ : HilbertVector R => ψ i)
    (applyVec_seq left right (state : HilbertVector R))

/-- Evolve a pure state whose physical placement is exactly the circuit layout.
Accounting remains a projection of the circuit or enclosing run. -/
@[nolint unusedArguments]
def apply {R : Register} (circuit : UnitaryCircuit R) (state : PureState R)
    (_hplacement : state.system_idx = circuit.physical_idx) : PureState R :=
  PureState.ofNormalized (circuit.applyNormalized state.state)
    state.system_idx

@[simp]
theorem identity_matrix (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) :
    ((identity R physical_idx physical_idx_nodup).matrix : HilbertOperator R) = 1 := rfl





@[simp]
theorem identity_eventCost (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) :
    (identity R physical_idx physical_idx_nodup).eventCost = 0 := rfl

@[simp]
theorem identity_eventTrace (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) :
    (identity R physical_idx physical_idx_nodup).eventTrace = [] := rfl

@[simp]
theorem identity_eventDepth (R : Register) (physical_idx : List Nat)
    (physical_idx_nodup : physical_idx.Nodup) :
    (identity R physical_idx physical_idx_nodup).eventDepth = .id := rfl

@[simp]
theorem leaf_matrix {R : Register} (leaf : UnitaryLeaf R)
    (systemIdxNodup : leaf.systemIdx.Nodup) :
    ((ofLeaf leaf systemIdxNodup).matrix : HilbertOperator R) =
      leaf.operator := rfl

@[simp]
theorem leaf_eventCost {R : Register} (leaf : UnitaryLeaf R)
    (systemIdxNodup : leaf.systemIdx.Nodup) :
    (ofLeaf leaf systemIdxNodup).eventCost =
      ResourcePool.singleton leaf.event := rfl

@[simp]
theorem leaf_eventTrace {R : Register} (leaf : UnitaryLeaf R)
    (systemIdxNodup : leaf.systemIdx.Nodup) :
    (ofLeaf leaf systemIdxNodup).eventTrace = [leaf.event] := rfl

@[simp]
theorem leaf_eventDepth {R : Register} (leaf : UnitaryLeaf R)
    (systemIdxNodup : leaf.systemIdx.Nodup) :
    (ofLeaf leaf systemIdxNodup).eventDepth = .atom leaf.event := rfl





@[simp]
theorem reindex_matrix {R S : Register} (equiv : R.Index ≃ S.Index)
    (circuit : UnitaryCircuit R) :
    (reindex equiv circuit).matrix = UnitaryOperator.reindex equiv circuit.matrix :=
  rfl





@[simp]
theorem reindex_eventCost {R S : Register} (equiv : R.Index ≃ S.Index)
    (circuit : UnitaryCircuit R) :
    (reindex equiv circuit).eventCost = circuit.eventCost := rfl

@[simp]
theorem reindex_eventTrace {R S : Register} (equiv : R.Index ≃ S.Index)
    (circuit : UnitaryCircuit R) :
    (reindex equiv circuit).eventTrace = circuit.eventTrace := rfl

@[simp]
theorem reindex_eventDepth {R S : Register} (equiv : R.Index ≃ S.Index)
    (circuit : UnitaryCircuit R) :
    (reindex equiv circuit).eventDepth = circuit.eventDepth := rfl

@[simp]
theorem seq_matrix {R : Register} (left right : UnitaryCircuit R) :
    ((seq left right).matrix : HilbertOperator R) =
      (right.matrix : HilbertOperator R) * (left.matrix : HilbertOperator R) := rfl





@[simp]
theorem seq_eventCost {R : Register} (left right : UnitaryCircuit R) :
    (seq left right).eventCost = left.eventCost + right.eventCost := rfl

@[simp]
theorem seq_eventTrace {R : Register} (left right : UnitaryCircuit R) :
    (seq left right).eventTrace = left.eventTrace ++ right.eventTrace := rfl

@[simp]
theorem seq_eventDepth {R : Register} (left right : UnitaryCircuit R) :
    (seq left right).eventDepth =
      .seq left.eventDepth right.eventDepth := rfl

@[simp]
theorem evaluatedEventDepth_seq {R : Register}
    (assign : Resource.Event .quantum → Nat) (left right : UnitaryCircuit R) :
    (seq left right).evaluatedEventDepth assign =
      left.evaluatedEventDepth assign + right.evaluatedEventDepth assign := rfl

@[simp]
theorem eventQueryDepth_seq {R : Register} (focus : Resource.Event .quantum)
    (left right : UnitaryCircuit R) :
    (seq left right).eventQueryDepth focus =
      left.eventQueryDepth focus + right.eventQueryDepth focus := rfl





@[simp]
theorem dagger_physical_idx {R : Register} (body : UnitaryCircuit R) :
    body.dagger.physical_idx = body.physical_idx := rfl

@[simp]
theorem dagger_matrix {R : Register} (body : UnitaryCircuit R) :
    (body.dagger.matrix : HilbertOperator R) =
      (body.matrix : HilbertOperator R).conjTranspose := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl



@[simp]
theorem dagger_eventTrace {R : Register} (body : UnitaryCircuit R) :
    body.dagger.eventTrace = body.eventTrace.reverse := rfl

@[simp]
theorem dagger_eventCost {R : Register} (body : UnitaryCircuit R) :
    body.dagger.eventCost = body.eventCost := rfl



@[simp]
theorem dagger_eventDepth {R : Register} (body : UnitaryCircuit R) :
    body.dagger.eventDepth = .inverse body.eventDepth := rfl

@[simp]
theorem evaluatedEventDepth_dagger {R : Register}
    (assign : Resource.Event .quantum → Nat) (body : UnitaryCircuit R) :
    body.dagger.evaluatedEventDepth assign = body.evaluatedEventDepth assign := rfl

@[simp]
theorem eventQueryDepth_dagger {R : Register}
    (focus : Resource.Event .quantum) (body : UnitaryCircuit R) :
    body.dagger.eventQueryDepth focus = body.eventQueryDepth focus := rfl





@[simp]
theorem iterate_matrix {R : Register} (count : Nat) (body : UnitaryCircuit R) :
    ((iterate count body).matrix : HilbertOperator R) =
      (body.matrix : HilbertOperator R) ^ count := rfl





@[simp]
theorem iterate_eventCost {R : Register} (count : Nat) (body : UnitaryCircuit R) :
    (iterate count body).eventCost = count • body.eventCost := rfl

@[simp]
theorem iterate_eventTrace {R : Register} (count : Nat) (body : UnitaryCircuit R) :
    (iterate count body).eventTrace =
      (List.replicate count body.eventTrace).flatten := rfl

@[simp]
theorem iterate_eventDepth {R : Register} (count : Nat) (body : UnitaryCircuit R) :
    (iterate count body).eventDepth = .iterate count body.eventDepth := rfl

@[simp]
theorem evaluatedEventDepth_iterate {R : Register}
    (assign : Resource.Event .quantum → Nat) (count : Nat) (body : UnitaryCircuit R) :
    (iterate count body).evaluatedEventDepth assign =
      count * body.evaluatedEventDepth assign := rfl

@[simp]
theorem eventQueryDepth_iterate {R : Register}
    (focus : Resource.Event .quantum) (count : Nat) (body : UnitaryCircuit R) :
    (iterate count body).eventQueryDepth focus =
      count * body.eventQueryDepth focus := rfl





@[simp]
theorem sequenceList_nil {R : Register} (start : UnitaryCircuit R) :
    sequenceList start [] = start := rfl

@[simp]
theorem sequenceList_cons {R : Register} (start step : UnitaryCircuit R)
    (steps : List (UnitaryCircuit R)) :
    sequenceList start (step :: steps) = sequenceList (seq start step) steps := rfl

@[simp]
theorem sequenceList_matrix {R : Register} (start : UnitaryCircuit R)
    (steps : List (UnitaryCircuit R)) :
    ((sequenceList start steps).matrix : HilbertOperator R) =
      steps.foldl
        (fun accumulated next => (next.matrix : HilbertOperator R) * accumulated)
        (start.matrix : HilbertOperator R) := by
  induction steps generalizing start with
  | nil => rfl
  | cons step steps ih =>
      change ((sequenceList (seq start step) steps).matrix : HilbertOperator R) = _
      simpa using ih (seq start step)

@[simp]
theorem indexedProductNamed_matrix {R : Register} (label : String) (count : Nat)
    (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) :
    ((indexedProductNamed label count start step).matrix : HilbertOperator R) =
      (List.ofFn (fun j => ((step j).matrix : HilbertOperator R))).foldl
        (fun accumulated next => next * accumulated)
        (start.matrix : HilbertOperator R) := by
  change
    (((List.ofFn (fun j => (step j).sequence.toUnitary)).foldl
        (fun accumulated next => next * accumulated) start.sequence.toUnitary :
        UnitaryOperator R) : HilbertOperator R) =
      (List.ofFn (fun j => ((step j).sequence.toUnitary : HilbertOperator R))).foldl
        (fun accumulated next => next * accumulated)
        (start.sequence.toUnitary : HilbertOperator R)
  have hmap :
      List.map (fun next : UnitaryOperator R => (next : HilbertOperator R))
          (List.ofFn (fun j => (step j).sequence.toUnitary)) =
        List.ofFn (fun j => ((step j).sequence.toUnitary : HilbertOperator R)) := by
    exact (List.ofFn_comp' (fun j => (step j).sequence.toUnitary)
      (fun next : UnitaryOperator R => (next : HilbertOperator R))).symm
  rw [← hmap]
  exact UnitarySequence.coe_foldl_unitary start.sequence.toUnitary
    (List.ofFn fun j => (step j).sequence.toUnitary)

/-- The indexed circuit product applies its members in increasing list order,
starting after the stored initial circuit. -/
theorem applyVec_indexedProductNamed {R : Register} (label : String)
    (count : Nat) (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R)
    (state : HilbertVector R) :
    (indexedProductNamed label count start step).applyVec state =
      (List.ofFn step).foldl
        (fun accumulated next => next.applyVec accumulated)
        (start.applyVec state) := by
  have foldl_applyVec : ∀ (circuits : List (UnitaryCircuit R))
      (initial : HilbertOperator R),
      HilbertOperator.applyVec
          ((circuits.map fun circuit =>
            (circuit.matrix : HilbertOperator R)).foldl
            (fun accumulated next => next * accumulated) initial) state =
        circuits.foldl
          (fun accumulated next => next.applyVec accumulated)
          (HilbertOperator.applyVec initial state) := by
    intro circuits initial
    induction circuits generalizing initial with
    | nil => rfl
    | cons circuit rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [ih, HilbertOperator.mul_applyVec]
        rfl
  change HilbertOperator.applyVec
      ((indexedProductNamed label count start step).matrix : HilbertOperator R)
      state = _
  rw [indexedProductNamed_matrix]
  have matrixList :
      List.ofFn (fun index : Fin count =>
          ((step index).matrix : HilbertOperator R)) =
        (List.ofFn step).map fun circuit =>
          (circuit.matrix : HilbertOperator R) :=
    List.ofFn_comp' step fun circuit =>
      (circuit.matrix : HilbertOperator R)
  rw [matrixList]
  exact foldl_applyVec (List.ofFn step) start.matrix

/-- Normalized-vector form of the increasing-order indexed product action. -/
theorem applyNormalized_indexedProductNamed {R : Register} (label : String)
    (count : Nat) (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R)
    (state : NormalizedVector R) :
    (indexedProductNamed label count start step).applyNormalized state =
      (List.ofFn step).foldl
        (fun accumulated next => next.applyNormalized accumulated)
        (start.applyNormalized state) := by
  have foldl_coe : ∀ (circuits : List (UnitaryCircuit R))
      (initial : NormalizedVector R),
      (((circuits.foldl
          (fun accumulated next => next.applyNormalized accumulated)
          initial : NormalizedVector R) : HilbertVector R)) =
        circuits.foldl
          (fun accumulated next => next.applyVec accumulated)
          (initial : HilbertVector R) := by
    intro circuits initial
    induction circuits generalizing initial with
    | nil => rfl
    | cons circuit rest ih =>
        simp only [List.foldl_cons]
        simpa using ih (circuit.applyNormalized initial)
  apply NormalizedVector.ext
  intro index
  have action :=
    applyVec_indexedProductNamed label count start step
      (state : HilbertVector R)
  have outputCoe := foldl_coe (List.ofFn step) (start.applyNormalized state)
  exact congrArg (fun output : HilbertVector R => output index)
    (action.trans (by simpa using outputCoe.symm))





@[simp]
theorem indexedProductNamed_eventCost {R : Register} (label : String) (count : Nat)
    (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) :
    (indexedProductNamed label count start step).eventCost =
      start.eventCost + ∑ j, (step j).eventCost := rfl

@[simp]
theorem indexedProductNamed_eventTrace {R : Register} (label : String)
    (count : Nat) (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) :
    (indexedProductNamed label count start step).eventTrace =
      start.eventTrace ++
        (List.ofFn fun j => (step j).eventTrace).flatten := rfl

@[simp]
theorem indexedProductNamed_eventDepth {R : Register} (label : String) (count : Nat)
    (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) :
    (indexedProductNamed label count start step).eventDepth =
      .indexedProduct label count start.eventDepth (fun j => (step j).eventDepth) := rfl

@[simp]
theorem evaluatedEventDepth_indexedProductNamed {R : Register}
    (assign : Resource.Event .quantum → Nat) (label : String) (count : Nat)
    (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) :
    (indexedProductNamed label count start step).evaluatedEventDepth assign =
      start.evaluatedEventDepth assign +
        ∑ j, (step j).evaluatedEventDepth assign := rfl

@[simp]
theorem eventQueryDepth_indexedProductNamed {R : Register}
    (focus : Resource.Event .quantum) (label : String) (count : Nat)
    (start : UnitaryCircuit R) (step : Fin count → UnitaryCircuit R) :
    (indexedProductNamed label count start step).eventQueryDepth focus =
      start.eventQueryDepth focus + ∑ j, (step j).eventQueryDepth focus := rfl





namespace UnitaryLeafFixtures

private def gateLabel : Resource.GateLabel :=
  .builtin "fixture-gate"

private def subroutineLabel : Resource.SubroutineLabel :=
  { family := "fixture", name := "opaque-subroutine" }

/-- Gate and subroutine event coordinates are independently visible in one
sequenced circuit, while semantics uses the same two sealed leaves. -/
example (gateLeaf subroutineLeaf : UnitaryLeaf (Qubits 1))
    (gateSystemIdxNodup : gateLeaf.systemIdx.Nodup)
    (subroutineSystemIdxNodup : subroutineLeaf.systemIdx.Nodup)
    (gateRole : gateLeaf.role = .gate gateLabel)
    (subroutineRole : subroutineLeaf.role = .subroutine subroutineLabel) :
    let gate := ofLeaf gateLeaf gateSystemIdxNodup
    let subroutine := ofLeaf subroutineLeaf subroutineSystemIdxNodup
    (seq gate subroutine).matrix =
        subroutineLeaf.operator * gateLeaf.operator ∧
      ResourcePool.count (.gate gateLabel) (seq gate subroutine).eventCost = 1 ∧
      ResourcePool.count (.quantumSubroutine subroutineLabel.quantum)
        (seq gate subroutine).eventCost = 1 := by
  dsimp only
  constructor
  · rfl
  constructor <;>
    simp [ResourcePool.count, ResourcePool.singleton, UnitaryLeaf.event,
      UnitaryLeafRole.event, gateRole, subroutineRole]

/-- The strict event-depth linearization is definitionally coherent with the
strict event pool for a mixed leaf sequence. -/
example (gateLeaf subroutineLeaf : UnitaryLeaf (Qubits 1))
    (gateSystemIdxNodup : gateLeaf.systemIdx.Nodup)
    (subroutineSystemIdxNodup : subroutineLeaf.systemIdx.Nodup) :
    let gate := ofLeaf gateLeaf gateSystemIdxNodup
    let subroutine := ofLeaf subroutineLeaf subroutineSystemIdxNodup
    (seq gate subroutine).resourcesFromEventDepth =
      (seq gate subroutine).eventCost := by
  simp

end UnitaryLeafFixtures

end

end UnitaryCircuit

end QuantumAlg

end
