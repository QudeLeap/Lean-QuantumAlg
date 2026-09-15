/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.Accounting.Flow
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum

/-!
# Layout-derived circuit space

A qubit circuit receives a live-space interpretation only together with an
actual `QubitLayout n` that contains its touched physical footprint.  The
layout is the complete input/output interface; the circuit footprint records
only systems touched by its sealed syntax.  In particular, an empty footprint
on a nonempty interface is not treated as a zero-qubit layout.

Each interface qubit retains its physical identity in the native quantum
layout and contributes one system to the dimension-two space coordinate.

The interface is borrowed: applying a circuit does not allocate or release its
input/output storage.  Resident space therefore contains the complete layout,
while the isolated circuit contributes no auxiliary space.  Ownership and
additional work layouts belong to the surrounding typed execution flow.

`interfaceContext` is a canonical observation context, not an execution-time
storage-key allocator.  Canonical child contexts intentionally reuse one key
and are therefore not combined with `SpaceFlow.tensor`; parallel Circuit laws
first form one proven-disjoint merged layout and interpret that layout once.
The typed execution owns fresh runtime keys and trace-level composition.
-/

section

namespace QuantumAlg

namespace UnitaryCircuit

noncomputable section

/-- Stable private identity used only for the canonical borrowed interface
context.  Its numeric value is not a space magnitude. -/
def interfaceStorageKey : StorageKey := ⟨0⟩

/-- Canonical live context for one borrowed qubit interface. -/
def interfaceContext {qubitCount : Nat}
    (layout : QubitLayout qubitCount) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedLayout interfaceStorageKey layout.toQuantumLayout
    (by change interfaceStorageKey ∉ ([] : List StorageKey); simp)
    (by change List.Disjoint layout.toQuantumLayout.identities []; simp)

/-- Interface-only liveness flow of a fully placed qubit circuit.

The containment proof is the admission boundary: generic circuit syntax has
no space interpretation until an actual complete interface layout is
provided.  The proof is intentionally erased from the resulting stay trace:
proof irrelevance ensures that two proofs of the same placement cannot change
space accounting. -/
@[nolint unusedArguments]
def interfaceSpaceFlow {qubitCount : Nat}
    (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (_contained : circuit.physical_idx ⊆ layout.systemIdx) :
    SpaceFlow (interfaceContext layout) (interfaceContext layout) :=
  SpaceFlow.stay (interfaceContext layout)

@[simp] theorem interfaceContext_physicalIdx {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    (interfaceContext layout).physicalIdx = layout.systemIdx := by
  rw [RuntimeCtx.physicalIdx_eq_flatMap]
  change [RuntimeEntry.borrowedLayout interfaceStorageKey layout.toQuantumLayout].flatMap
    RuntimeEntry.physicalIdx = _
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change (List.ofFn layout.toQuantumLayout.wire).map QuantumWire.identity = _
  rw [List.map_ofFn]
  rfl

@[simp] theorem interfaceContext_residentSpace {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    (interfaceContext layout).residentSpace =
      SpacePool.ofQuantumLayout layout.toQuantumLayout := by
  simp [interfaceContext]

@[simp] theorem interfaceContext_auxiliarySpace {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    (interfaceContext layout).auxiliarySpace = 0 := by
  simp [interfaceContext]

@[simp] theorem interfaceSpaceFlow_peakResidentSpace {qubitCount : Nat}
    (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : circuit.physical_idx ⊆ layout.systemIdx) :
    (interfaceSpaceFlow circuit layout contained).peakResidentSpace =
      SpacePool.ofQuantumLayout layout.toQuantumLayout := by
  simp [interfaceSpaceFlow]

@[simp] theorem interfaceSpaceFlow_peakAuxiliarySpace {qubitCount : Nat}
    (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : circuit.physical_idx ⊆ layout.systemIdx) :
    (interfaceSpaceFlow circuit layout contained).peakAuxiliarySpace = 0 := by
  simp [interfaceSpaceFlow]

theorem interfaceSpaceFlow_classicalBits {qubitCount : Nat}
    (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : circuit.physical_idx ⊆ layout.systemIdx) :
    SpacePool.count .classicalBits
        (interfaceSpaceFlow circuit layout contained).peakResidentSpace = 0 := by
  simp

theorem interfaceSpaceFlow_qubits {qubitCount : Nat}
    (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : circuit.physical_idx ⊆ layout.systemIdx) :
    SpacePool.count (.quantumSystems 2)
        (interfaceSpaceFlow circuit layout contained).peakResidentSpace =
      qubitCount := by
  simp [QubitLayout.toQuantumLayout_dimensionCount]

/-! ## Constructor footprint admission -/

/-- An identity circuit is layout-aware exactly when its explicit touched
footprint lies in the complete interface. -/
theorem identity_physical_idx_subset_layout {qubitCount : Nat}
    (physicalIdx : List Nat) (physicalIdxNodup : physicalIdx.Nodup)
    (layout : QubitLayout qubitCount)
    (contained : physicalIdx ⊆ layout.systemIdx) :
    (identity (Qubits qubitCount) physicalIdx physicalIdxNodup).physical_idx ⊆
      layout.systemIdx :=
  contained

/-- A leaf is admitted by the complete interface containing its actual
placement. -/
theorem ofLeaf_physical_idx_subset_layout {qubitCount : Nat}
    (leaf : UnitaryLeaf (Qubits qubitCount))
    (systemIdxNodup : leaf.systemIdx.Nodup)
    (layout : QubitLayout qubitCount)
    (contained : leaf.systemIdx ⊆ layout.systemIdx) :
    (ofLeaf leaf systemIdxNodup).physical_idx ⊆ layout.systemIdx :=
  contained

/-- `ofLeafAt` uses its explicit enclosing footprint; the leaf-subset proof
does not turn that footprint into a claimed live-space magnitude. -/
theorem ofLeafAt_physical_idx_subset_layout {qubitCount : Nat}
    (physicalIdx : List Nat) (leaf : UnitaryLeaf (Qubits qubitCount))
    (physicalIdxNodup : physicalIdx.Nodup)
    (leafSystemIdxNodup : leaf.systemIdx.Nodup)
    (leafContained : leaf.systemIdx ⊆ physicalIdx)
    (layout : QubitLayout qubitCount)
    (contained : physicalIdx ⊆ layout.systemIdx) :
    (ofLeafAt physicalIdx leaf physicalIdxNodup leafSystemIdxNodup
      leafContained).physical_idx ⊆ layout.systemIdx :=
  contained

/-- Adjoint preserves the touched footprint and hence the same complete
interface admission proof. -/
theorem dagger_physical_idx_subset_layout {qubitCount : Nat}
    (body : UnitaryCircuit (Qubits qubitCount)) (layout : QubitLayout qubitCount)
    (contained : body.physical_idx ⊆ layout.systemIdx) :
    (dagger body).physical_idx ⊆ layout.systemIdx :=
  contained

/-- Fixed repetition preserves one live interface; its space is not multiplied
by the iteration count. -/
theorem iterate_physical_idx_subset_layout {qubitCount : Nat}
    (count : Nat) (body : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : body.physical_idx ⊆ layout.systemIdx) :
    (iterate count body).physical_idx ⊆ layout.systemIdx :=
  contained

/-- Logical reindexing preserves the physical footprint.  The target still
needs its own actual complete `QubitLayout`. -/
theorem reindex_physical_idx_subset_layout {sourceCount targetCount : Nat}
    (equiv : (Qubits sourceCount).Index ≃ (Qubits targetCount).Index)
    (body : UnitaryCircuit (Qubits sourceCount))
    (layout : QubitLayout targetCount)
    (contained : body.physical_idx ⊆ layout.systemIdx) :
    (reindex equiv body).physical_idx ⊆ layout.systemIdx :=
  contained

/-- Physical relabeling must supply a complete target layout containing the
new footprint; no space is inferred from the old labels. -/
theorem relabel_physical_idx_subset_layout {qubitCount : Nat}
    (body : UnitaryCircuit (Qubits qubitCount)) {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling body.physical_idx newPhysicalIdx)
    (layout : QubitLayout qubitCount)
    (contained : newPhysicalIdx ⊆ layout.systemIdx) :
    (relabel body relabeling).physical_idx ⊆ layout.systemIdx :=
  contained

/-- Two circuit blocks whose touched footprints both lie in the same complete
interface remain in that interface after sequential composition. -/
theorem seq_physical_idx_subset_layout {qubitCount : Nat}
    (left right : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (leftContained : left.physical_idx ⊆ layout.systemIdx)
    (rightContained : right.physical_idx ⊆ layout.systemIdx) :
    (seq left right).physical_idx ⊆ layout.systemIdx := by
  intro index hindex
  change index ∈ left.physical_idx.union right.physical_idx at hindex
  rcases List.mem_union_iff.mp hindex with hleft | hright
  · exact leftContained hleft
  · exact rightContained hright

/-- A stable fold of touched-footprint unions remains inside a common complete
interface when its initial and every added footprint do. -/
theorem foldl_unionPhysicalIdx_subset (layouts : List (List Nat))
    (initial target : List Nat) (initialContained : initial ⊆ target)
    (layoutsContained : ∀ footprint ∈ layouts, footprint ⊆ target) :
    layouts.foldl unionPhysicalIdx initial ⊆ target := by
  induction layouts generalizing initial with
  | nil => exact initialContained
  | cons footprint layouts ih =>
      apply ih (initial := unionPhysicalIdx initial footprint)
      · intro index hindex
        rcases List.mem_union_iff.mp hindex with hinitial | hfootprint
        · exact initialContained hinitial
        · exact layoutsContained footprint (by simp) hfootprint
      · intro next hnext
        exact layoutsContained next (by simp [hnext])

/-- Every block of an explicit sequence uses one compatible complete
interface. -/
theorem sequenceList_physical_idx_subset_layout {qubitCount : Nat}
    (start : UnitaryCircuit (Qubits qubitCount))
    (steps : List (UnitaryCircuit (Qubits qubitCount)))
    (layout : QubitLayout qubitCount)
    (startContained : start.physical_idx ⊆ layout.systemIdx)
    (stepsContained : ∀ step ∈ steps, step.physical_idx ⊆ layout.systemIdx) :
    (sequenceList start steps).physical_idx ⊆ layout.systemIdx := by
  induction steps generalizing start with
  | nil => exact startContained
  | cons step steps ih =>
      apply ih (start := seq start step)
      · exact seq_physical_idx_subset_layout start step layout startContained
          (stepsContained step (by simp))
      · intro next hnext
        exact stepsContained next (by simp [hnext])

/-- A symbolic indexed product is admitted only when its start and every
actual indexed step fit one complete interface. -/
theorem indexedProductNamed_physical_idx_subset_layout {qubitCount : Nat}
    (label : String) (count : Nat) (start : UnitaryCircuit (Qubits qubitCount))
    (step : Fin count → UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (startContained : start.physical_idx ⊆ layout.systemIdx)
    (stepsContained : ∀ j, (step j).physical_idx ⊆ layout.systemIdx) :
    (indexedProductNamed label count start step).physical_idx ⊆
      layout.systemIdx := by
  apply foldl_unionPhysicalIdx_subset
  · exact startContained
  · intro footprint hfootprint
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hfootprint
    exact stepsContained j

/-- Unlabelled indexed products use the same common-interface rule. -/
theorem indexedProduct_physical_idx_subset_layout {qubitCount : Nat}
    (count : Nat) (start : UnitaryCircuit (Qubits qubitCount))
    (step : Fin count → UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (startContained : start.physical_idx ⊆ layout.systemIdx)
    (stepsContained : ∀ j, (step j).physical_idx ⊆ layout.systemIdx) :
    (indexedProduct count start step).physical_idx ⊆ layout.systemIdx :=
  indexedProductNamed_physical_idx_subset_layout "indexed-product" count
    start step layout startContained stepsContained

/-- Schedule-indexed products expose every actual `Fin schedule.length` step
to the same layout admission proof. -/
theorem indexedProductList_physical_idx_subset_layout
    {qubitCount : Nat} {scheduleType : Type} (label : String)
    (start : UnitaryCircuit (Qubits qubitCount)) (schedule : List scheduleType)
    (step : scheduleType → UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (startContained : start.physical_idx ⊆ layout.systemIdx)
    (stepsContained : ∀ j : Fin schedule.length,
      (step (schedule.get j)).physical_idx ⊆ layout.systemIdx) :
    (indexedProductList label start schedule step).physical_idx ⊆
      layout.systemIdx :=
  indexedProductNamed_physical_idx_subset_layout label schedule.length start
    (fun j => step (schedule.get j)) layout startContained stepsContained

/-- Sequential composition visits one shared live interface and therefore
takes the pointwise maximum of the two interface-only resident peaks. -/
theorem interfaceSpaceFlow_seq_peakResidentSpace
    {qubitCount : Nat} (left right : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (leftContained : left.physical_idx ⊆ layout.systemIdx)
    (rightContained : right.physical_idx ⊆ layout.systemIdx) :
    (interfaceSpaceFlow (seq left right) layout
        (seq_physical_idx_subset_layout left right layout
          leftContained rightContained)).peakResidentSpace =
      SpacePool.max
        (interfaceSpaceFlow left layout leftContained).peakResidentSpace
        (interfaceSpaceFlow right layout rightContained).peakResidentSpace := by
  simp

/-- Sequential composition takes the pointwise maximum of the two
interface-only auxiliary peaks (both are zero for a borrowed interface). -/
theorem interfaceSpaceFlow_seq_peakAuxiliarySpace
    {qubitCount : Nat} (left right : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (leftContained : left.physical_idx ⊆ layout.systemIdx)
    (rightContained : right.physical_idx ⊆ layout.systemIdx) :
    (interfaceSpaceFlow (seq left right) layout
        (seq_physical_idx_subset_layout left right layout
          leftContained rightContained)).peakAuxiliarySpace =
      SpacePool.max
        (interfaceSpaceFlow left layout leftContained).peakAuxiliarySpace
        (interfaceSpaceFlow right layout rightContained).peakAuxiliarySpace := by
  simp

/-- Circuit labels, operators, and hidden implementations cannot change the
resident peak of one explicitly fixed interface. -/
theorem interfaceSpaceFlow_sameInterface_peakResidentSpace
    {qubitCount : Nat} (left right : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (leftContained : left.physical_idx ⊆ layout.systemIdx)
    (rightContained : right.physical_idx ⊆ layout.systemIdx) :
    (interfaceSpaceFlow left layout leftContained).peakResidentSpace =
      (interfaceSpaceFlow right layout rightContained).peakResidentSpace := by
  simp

/-- Circuit labels, operators, and hidden implementations cannot change the
auxiliary peak of one explicitly fixed interface. -/
theorem interfaceSpaceFlow_sameInterface_peakAuxiliarySpace
    {qubitCount : Nat} (left right : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (leftContained : left.physical_idx ⊆ layout.systemIdx)
    (rightContained : right.physical_idx ⊆ layout.systemIdx) :
    (interfaceSpaceFlow left layout leftContained).peakAuxiliarySpace =
      (interfaceSpaceFlow right layout rightContained).peakAuxiliarySpace := by
  simp

/-- Capacity-only comparison with a separately constructed expanded flow.

This theorem does not assert that `expanded` implements `circuit`, nor that the
exact `layout` occurs as an entry in `pre`; those semantic/layout relations
must be supplied by an independent theorem about the concrete expanded object.
It only transports the explicit entry-capacity hypothesis to a peak bound and
never rewrites the opaque interface-only coordinate. -/
theorem interfaceSpaceFlow_peakResidentSpace_le_expandedCapacity
    {qubitCount : Nat} (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : circuit.physical_idx ⊆ layout.systemIdx)
    {pre post : RuntimeCtx .quantum} (expanded : SpaceFlow pre post)
    (entryCapacity : SpacePool.ofQuantumLayout layout.toQuantumLayout ≤ pre.residentSpace) :
    (interfaceSpaceFlow circuit layout contained).peakResidentSpace ≤
      expanded.peakResidentSpace := by
  rw [interfaceSpaceFlow_peakResidentSpace]
  exact entryCapacity.trans (SpaceFlow.residentSpace_pre_le_peak expanded)

/-- The isolated borrowed interface contributes no auxiliary space, so every
separately constructed expanded execution dominates that auxiliary peak. -/
theorem interfaceSpaceFlow_peakAuxiliarySpace_le_expandedCapacity
    {qubitCount : Nat} (circuit : UnitaryCircuit (Qubits qubitCount))
    (layout : QubitLayout qubitCount)
    (contained : circuit.physical_idx ⊆ layout.systemIdx)
    {pre post : RuntimeCtx .quantum} (expanded : SpaceFlow pre post) :
    (interfaceSpaceFlow circuit layout contained).peakAuxiliarySpace ≤
      expanded.peakAuxiliarySpace := by
  simp

end

end UnitaryCircuit

end QuantumAlg

end
