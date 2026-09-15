/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Space
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import Mathlib.Data.List.Nodup
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Physical-layout calculus for typed circuits

Logical register positions and physical system indices are separate. A
`PhysicalLayout.Relabeling old new` records one positional relabeling, while a
`PhysicalLayout.DisjointMerge left right` certifies that parallel layouts may
be concatenated without aliasing.

Relabeling rewrites every sealed leaf's `systemIdx` through the same function.
It leaves the unitary operator, ordered event trace, event pool, and symbolic
event depth unchanged. This means that changing a circuit layout also rewrites
every child gate placement without changing operator or accounting semantics.
-/

section

namespace QuantumAlg

open Kronecker

namespace UnitarySequence

@[simp]
theorem toUnitary_rewriteSystemIdx {R : Register} (mapping : Nat → Nat)
    (sequence : UnitarySequence R) :
    (sequence.rewriteSystemIdx mapping).toUnitary = sequence.toUnitary := by
  induction sequence with
  | id => rfl
  | leaf => rfl
  | seq left right ihLeft ihRight =>
      simp [rewriteSystemIdx, toUnitary, ihLeft, ihRight]
  | tensor left right ihLeft ihRight =>
      simp [rewriteSystemIdx, toUnitary, ihLeft, ihRight]
  | reindex equiv body ih =>
      simp [rewriteSystemIdx, toUnitary, ih]
  | dagger body ih =>
      simp [rewriteSystemIdx, toUnitary, ih]
  | controlled control activationValue body ih =>
      simp [rewriteSystemIdx, toUnitary, ih]
  | iterate count body ih =>
      simp [rewriteSystemIdx, toUnitary, ih]
  | indexedProduct label count start step ihStart ihStep =>
      simp [rewriteSystemIdx, toUnitary, ihStart, ihStep]

@[simp]
theorem eventTrace_rewriteSystemIdx {R : Register} (mapping : Nat → Nat)
    (sequence : UnitarySequence R) :
    (sequence.rewriteSystemIdx mapping).eventTrace = sequence.eventTrace := by
  induction sequence with
  | id => rfl
  | leaf => rfl
  | seq left right ihLeft ihRight =>
      simp [rewriteSystemIdx, eventTrace, ihLeft, ihRight]
  | tensor left right ihLeft ihRight =>
      simp [rewriteSystemIdx, eventTrace, ihLeft, ihRight]
  | reindex equiv body ih => simp [rewriteSystemIdx, eventTrace, ih]
  | dagger body ih => simp [rewriteSystemIdx, eventTrace, ih]
  | controlled control activationValue body ih =>
      simp [rewriteSystemIdx, eventTrace, ih]
  | iterate count body ih => simp [rewriteSystemIdx, eventTrace, ih]
  | indexedProduct label count start step ihStart ihStep =>
      simp [rewriteSystemIdx, eventTrace, ihStart, ihStep]

@[simp]
theorem eventCost_rewriteSystemIdx {R : Register} (mapping : Nat → Nat)
    (sequence : UnitarySequence R) :
    (sequence.rewriteSystemIdx mapping).eventCost = sequence.eventCost := by
  induction sequence with
  | id => rfl
  | leaf => rfl
  | seq left right ihLeft ihRight =>
      simp [rewriteSystemIdx, eventCost, ihLeft, ihRight]
  | tensor left right ihLeft ihRight =>
      simp [rewriteSystemIdx, eventCost, ihLeft, ihRight]
  | reindex equiv body ih => simp [rewriteSystemIdx, eventCost, ih]
  | dagger body ih => simp [rewriteSystemIdx, eventCost, ih]
  | controlled control activationValue body ih =>
      simp [rewriteSystemIdx, eventCost, ih]
  | iterate count body ih => simp [rewriteSystemIdx, eventCost, ih]
  | indexedProduct label count start step ihStart ihStep =>
      simp [rewriteSystemIdx, eventCost, ihStart, ihStep]

@[simp]
theorem eventDepth_rewriteSystemIdx {R : Register} (mapping : Nat → Nat)
    (sequence : UnitarySequence R) :
    (sequence.rewriteSystemIdx mapping).eventDepth = sequence.eventDepth := by
  induction sequence with
  | id => rfl
  | leaf => rfl
  | seq left right ihLeft ihRight =>
      simp [rewriteSystemIdx, eventDepth, ihLeft, ihRight]
  | tensor left right ihLeft ihRight =>
      simp [rewriteSystemIdx, eventDepth, ihLeft, ihRight]
  | reindex equiv body ih => simp [rewriteSystemIdx, eventDepth, ih]
  | dagger body ih => simp [rewriteSystemIdx, eventDepth, ih]
  | controlled control activationValue body ih =>
      simp [rewriteSystemIdx, eventDepth, ih]
  | iterate count body ih => simp [rewriteSystemIdx, eventDepth, ih]
  | indexedProduct label count start step ihStart ihStep =>
      simp [rewriteSystemIdx, eventDepth, ihStart, ihStep]





end UnitarySequence

namespace UnitaryCircuit

noncomputable section

/-- Shift every physical wire of a circuit by a fixed offset, preserving its
logical operator and complete sealed construction tree. -/
def shiftPhysicalIdx {R : Register} (offset : Nat) (circuit : UnitaryCircuit R) :
    UnitaryCircuit R :=
  relabel circuit
    { toFun := fun index => offset + index
      map_layout := rfl
      old_nodup := circuit.physical_idx_nodup
      new_nodup := circuit.physical_idx_nodup.map (fun _ _ equal =>
        Nat.add_left_cancel equal) }

@[simp]
theorem shiftPhysicalIdx_physical_idx {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (shiftPhysicalIdx offset circuit).physical_idx =
      circuit.physical_idx.map (fun index => offset + index) :=
  rfl

@[simp]
theorem shiftPhysicalIdx_matrix {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (shiftPhysicalIdx offset circuit).matrix = circuit.matrix := by
  exact UnitarySequence.toUnitary_rewriteSystemIdx _ circuit.sequence

@[simp]
theorem shiftPhysicalIdx_eventTrace {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (shiftPhysicalIdx offset circuit).eventTrace = circuit.eventTrace := by
  exact UnitarySequence.eventTrace_rewriteSystemIdx _ circuit.sequence





@[simp]
theorem shiftPhysicalIdx_eventCost {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (shiftPhysicalIdx offset circuit).eventCost = circuit.eventCost := by
  exact UnitarySequence.eventCost_rewriteSystemIdx _ circuit.sequence

@[simp]
theorem shiftPhysicalIdx_eventDepth {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (shiftPhysicalIdx offset circuit).eventDepth = circuit.eventDepth := by
  exact UnitarySequence.eventDepth_rewriteSystemIdx _ circuit.sequence

theorem shiftPhysicalIdx_resourcesFromEventDepth {R : Register} (offset : Nat)
    (circuit : UnitaryCircuit R) :
    (shiftPhysicalIdx offset circuit).resourcesFromEventDepth =
      circuit.resourcesFromEventDepth := by
  simp [resourcesFromEventDepth]

/-- A sequential composition stays inside any common physical footprint. -/
theorem seq_physical_idx_subset {R : Register} (left right : UnitaryCircuit R)
    {target : List Nat} (leftContained : left.physical_idx ⊆ target)
    (rightContained : right.physical_idx ⊆ target) :
    (seq left right).physical_idx ⊆ target := by
  intro index hindex
  change index ∈ left.physical_idx ∪ right.physical_idx at hindex
  rcases List.mem_union_iff.mp hindex with hleft | hright
  · exact leftContained hleft
  · exact rightContained hright

/-- Taking an adjoint preserves every proved physical-footprint inclusion. -/
theorem dagger_physical_idx_subset {R : Register} (body : UnitaryCircuit R)
    {target : List Nat} (contained : body.physical_idx ⊆ target) :
    body.dagger.physical_idx ⊆ target := by
  simpa only [dagger_physical_idx] using contained

/-- Reindexing the logical basis does not change a proved physical footprint. -/
theorem reindex_physical_idx_subset {R S : Register}
    (equiv : R.Index ≃ S.Index) (body : UnitaryCircuit R) {target : List Nat}
    (contained : body.physical_idx ⊆ target) :
    (reindex equiv body).physical_idx ⊆ target :=
  contained

/-- Symbolic repetition does not change a proved physical footprint. -/
theorem iterate_physical_idx_subset {R : Register}
    (count : Nat) (body : UnitaryCircuit R) {target : List Nat}
    (contained : body.physical_idx ⊆ target) :
    (iterate count body).physical_idx ⊆ target :=
  contained

/-- Shifting a canonical `n`-qubit footprint by an offset remains within the
corresponding larger canonical range. -/
theorem shiftPhysicalIdx_physical_idx_subset_range {n : Nat}
    (offset : Nat) (program : UnitaryCircuit (Qubits n))
    (contained : program.physical_idx ⊆ List.range n) :
    (shiftPhysicalIdx offset program).physical_idx ⊆ List.range (offset + n) := by
  intro index hindex
  rw [shiftPhysicalIdx_physical_idx] at hindex
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hindex
  have sourceLt : source < n := List.mem_range.mp (contained hsource)
  exact List.mem_range.mpr (by omega)

/-- Checked tensor product of two qubit circuits, flattened to the canonical
big-endian `(m+n)`-qubit basis while preserving the complete construction
tree. -/
def tensorQubits {m n : Nat} (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    UnitaryCircuit (Qubits (m + n)) :=
  reindex (prodEquiv (m := m) (n := n)) (tensor left right layout)

/-- A checked tensor of two circuits remains in any common admitted physical
footprint. -/
theorem tensorQubits_physical_idx_subset {m n : Nat}
    (left : UnitaryCircuit (Qubits m)) (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx)
    {target : List Nat} (leftContained : left.physical_idx ⊆ target)
    (rightContained : right.physical_idx ⊆ target) :
    (tensorQubits left right layout).physical_idx ⊆ target := by
  intro index hindex
  change index ∈ left.physical_idx ++ right.physical_idx at hindex
  rcases List.mem_append.mp hindex with hleft | hright
  · exact leftContained hleft
  · exact rightContained hright

/-- Add a leading qubit control and flatten the product register to the
canonical `(1+n)`-qubit basis without changing the underlying sequence. -/
def controlQubitsAt {n : Nat} (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) : UnitaryCircuit (Qubits (1 + n)) :=
  reindex (prodEquiv (m := 1) (n := n))
    (controlAt (Qubits 1) controlSystemIdx body layout activationValue)

/-- A checked leading-qubit control remains in any common admitted physical
footprint. -/
theorem controlQubitsAt_physical_idx_subset {n : Nat}
    (controlSystemIdx : List Nat) (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) {target : List Nat}
    (controlContained : controlSystemIdx ⊆ target)
    (bodyContained : body.physical_idx ⊆ target) :
    (controlQubitsAt controlSystemIdx body layout activationValue).physical_idx ⊆
      target := by
  intro index hindex
  change index ∈ controlSystemIdx ++ body.physical_idx at hindex
  rcases List.mem_append.mp hindex with hcontrol | hbody
  · exact controlContained hcontrol
  · exact bodyContained hbody

/-- Tensor two qubit circuits only after placing both touched footprints inside
actual complete, disjoint interfaces.  The result remains an ordinary
`UnitaryCircuit`; the layouts are proof inputs, not stored space metadata. -/
def tensorQubitsOnLayouts {m n : Nat} (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n)) (leftLayout : QubitLayout m)
    (rightLayout : QubitLayout n)
    (leftContained : left.physical_idx ⊆ leftLayout.systemIdx)
    (rightContained : right.physical_idx ⊆ rightLayout.systemIdx)
    (disjoint : List.Disjoint leftLayout.systemIdx rightLayout.systemIdx) :
    UnitaryCircuit (Qubits (m + n)) :=
  tensorQubits left right
    { left_nodup := left.physical_idx_nodup
      right_nodup := right.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left] at disjoint ⊢
        intro index hleft hright
        exact disjoint (leftContained hleft) (rightContained hright) }

/-- Add a one-qubit control using its actual complete layout and a complete
body layout.  Full-interface disjointness is stronger than merely checking the
body's touched footprint. -/
def controlQubitsAtOnLayouts {n : Nat} (controlLayout : QubitLayout 1)
    (body : UnitaryCircuit (Qubits n)) (bodyLayout : QubitLayout n)
    (bodyContained : body.physical_idx ⊆ bodyLayout.systemIdx)
    (disjoint : List.Disjoint controlLayout.systemIdx bodyLayout.systemIdx)
    (activationValue : Fin 2) : UnitaryCircuit (Qubits (1 + n)) :=
  controlQubitsAt controlLayout.systemIdx body
    { left_nodup := controlLayout.systemIdx_nodup
      right_nodup := body.physical_idx_nodup
      disjoint := by
        rw [List.disjoint_left] at disjoint ⊢
        intro index hcontrol hbody
        exact disjoint hcontrol (bodyContained hbody) }
    activationValue

/-- The checked tensor footprint lies inside the append of its two complete
interfaces. -/
theorem tensorQubitsOnLayouts_physical_idx_subset_appendLayout
    {m n : Nat} (left : UnitaryCircuit (Qubits m)) (right : UnitaryCircuit (Qubits n))
    (leftLayout : QubitLayout m) (rightLayout : QubitLayout n)
    (leftContained : left.physical_idx ⊆ leftLayout.systemIdx)
    (rightContained : right.physical_idx ⊆ rightLayout.systemIdx)
    (disjoint : List.Disjoint leftLayout.systemIdx rightLayout.systemIdx) :
    (tensorQubitsOnLayouts left right leftLayout rightLayout leftContained
        rightContained disjoint).physical_idx ⊆
      (QubitLayout.append leftLayout rightLayout disjoint).systemIdx := by
  intro index hindex
  change index ∈ left.physical_idx ++ right.physical_idx at hindex
  rw [QubitLayout.systemIdx_append]
  rcases List.mem_append.mp hindex with hleft | hright
  · exact List.mem_append_left _ (leftContained hleft)
  · exact List.mem_append_right _ (rightContained hright)

/-- The checked controlled footprint lies inside the append of the actual
control and body interfaces. -/
theorem controlQubitsAtOnLayouts_physical_idx_subset_appendLayout
    {n : Nat} (controlLayout : QubitLayout 1)
    (body : UnitaryCircuit (Qubits n)) (bodyLayout : QubitLayout n)
    (bodyContained : body.physical_idx ⊆ bodyLayout.systemIdx)
    (disjoint : List.Disjoint controlLayout.systemIdx bodyLayout.systemIdx)
    (activationValue : Fin 2) :
    (controlQubitsAtOnLayouts controlLayout body bodyLayout bodyContained
        disjoint activationValue).physical_idx ⊆
      (QubitLayout.append controlLayout bodyLayout disjoint).systemIdx := by
  intro index hindex
  change index ∈ controlLayout.systemIdx ++ body.physical_idx at hindex
  rw [QubitLayout.systemIdx_append]
  rcases List.mem_append.mp hindex with hcontrol | hbody
  · exact List.mem_append_left _ hcontrol
  · exact List.mem_append_right _ (bodyContained hbody)

/-- Parallel composition adds the two actually live interface peaks. -/
theorem interfaceSpaceFlow_tensorQubitsOnLayouts_peakResidentSpace
    {m n : Nat} (left : UnitaryCircuit (Qubits m)) (right : UnitaryCircuit (Qubits n))
    (leftLayout : QubitLayout m) (rightLayout : QubitLayout n)
    (leftContained : left.physical_idx ⊆ leftLayout.systemIdx)
    (rightContained : right.physical_idx ⊆ rightLayout.systemIdx)
    (disjoint : List.Disjoint leftLayout.systemIdx rightLayout.systemIdx) :
    SpaceFlow.peakResidentSpace (interfaceSpaceFlow
        (tensorQubitsOnLayouts left right leftLayout rightLayout leftContained
          rightContained disjoint)
        (QubitLayout.append leftLayout rightLayout disjoint)
        (tensorQubitsOnLayouts_physical_idx_subset_appendLayout left right
          leftLayout rightLayout leftContained rightContained disjoint)) =
        (interfaceSpaceFlow left leftLayout leftContained).peakResidentSpace +
          (interfaceSpaceFlow right rightLayout rightContained).peakResidentSpace := by
  ext axis
  cases axis with
  | classicalBits => simp [SpacePool.ofQuantumLayout]
  | quantumSystems dimension =>
      by_cases isQubit : (2 : ℕ+) = dimension <;>
        simp [SpacePool.ofQuantumLayout, QubitLayout.toQuantumLayout_dimensionCount, isQubit]

/-- Parallel composition adds the two interface-only auxiliary peaks. -/
theorem interfaceSpaceFlow_tensorQubitsOnLayouts_peakAuxiliarySpace
    {m n : Nat} (left : UnitaryCircuit (Qubits m)) (right : UnitaryCircuit (Qubits n))
    (leftLayout : QubitLayout m) (rightLayout : QubitLayout n)
    (leftContained : left.physical_idx ⊆ leftLayout.systemIdx)
    (rightContained : right.physical_idx ⊆ rightLayout.systemIdx)
    (disjoint : List.Disjoint leftLayout.systemIdx rightLayout.systemIdx) :
    SpaceFlow.peakAuxiliarySpace (interfaceSpaceFlow
        (tensorQubitsOnLayouts left right leftLayout rightLayout leftContained
          rightContained disjoint)
        (QubitLayout.append leftLayout rightLayout disjoint)
        (tensorQubitsOnLayouts_physical_idx_subset_appendLayout left right
          leftLayout rightLayout leftContained rightContained disjoint)) =
        (interfaceSpaceFlow left leftLayout leftContained).peakAuxiliarySpace +
          (interfaceSpaceFlow right rightLayout rightContained).peakAuxiliarySpace := by
  simp

/-- A checked control accounts for the actual control layout in addition to
the body's complete live interface. -/
theorem interfaceSpaceFlow_controlQubitsAtOnLayouts_peakResidentSpace
    {n : Nat} (controlLayout : QubitLayout 1)
    (body : UnitaryCircuit (Qubits n)) (bodyLayout : QubitLayout n)
    (bodyContained : body.physical_idx ⊆ bodyLayout.systemIdx)
    (disjoint : List.Disjoint controlLayout.systemIdx bodyLayout.systemIdx)
    (activationValue : Fin 2) :
    SpaceFlow.peakResidentSpace (interfaceSpaceFlow
        (controlQubitsAtOnLayouts controlLayout body bodyLayout bodyContained
          disjoint activationValue)
        (QubitLayout.append controlLayout bodyLayout disjoint)
        (controlQubitsAtOnLayouts_physical_idx_subset_appendLayout controlLayout
          body bodyLayout bodyContained disjoint activationValue)) =
        SpacePool.ofQuantumLayout controlLayout.toQuantumLayout +
          (interfaceSpaceFlow body bodyLayout bodyContained).peakResidentSpace := by
  ext axis
  cases axis with
  | classicalBits => simp [SpacePool.ofQuantumLayout]
  | quantumSystems dimension =>
      by_cases isQubit : (2 : ℕ+) = dimension <;>
        simp [SpacePool.ofQuantumLayout, QubitLayout.toQuantumLayout_dimensionCount, isQubit]

/-- A borrowed control interface contributes no auxiliary space. -/
theorem interfaceSpaceFlow_controlQubitsAtOnLayouts_peakAuxiliarySpace
    {n : Nat} (controlLayout : QubitLayout 1)
    (body : UnitaryCircuit (Qubits n)) (bodyLayout : QubitLayout n)
    (bodyContained : body.physical_idx ⊆ bodyLayout.systemIdx)
    (disjoint : List.Disjoint controlLayout.systemIdx bodyLayout.systemIdx)
    (activationValue : Fin 2) :
    SpaceFlow.peakAuxiliarySpace (interfaceSpaceFlow
        (controlQubitsAtOnLayouts controlLayout body bodyLayout bodyContained
          disjoint activationValue)
        (QubitLayout.append controlLayout bodyLayout disjoint)
        (controlQubitsAtOnLayouts_physical_idx_subset_appendLayout controlLayout
          body bodyLayout bodyContained disjoint activationValue)) =
        (interfaceSpaceFlow body bodyLayout bodyContained).peakAuxiliarySpace := by
  simp

@[simp]
theorem tensorQubits_matrix {m n : Nat} (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).matrix =
      UnitaryOperator.tensor left.matrix right.matrix :=
  rfl

@[simp]
theorem tensorQubits_eventTrace {m n : Nat} (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).eventTrace =
      left.eventTrace ++ right.eventTrace := rfl

@[simp]
theorem tensorQubits_eventCost {m n : Nat} (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).eventCost =
      left.eventCost + right.eventCost := rfl

@[simp]
theorem tensorQubits_eventDepth {m n : Nat} (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).eventDepth =
      .tensor left.eventDepth right.eventDepth := rfl

@[simp]
theorem evaluatedEventDepth_tensorQubits {m n : Nat}
    (assign : Resource.Event .quantum → Nat) (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).evaluatedEventDepth assign =
      max (left.evaluatedEventDepth assign) (right.evaluatedEventDepth assign) := rfl

@[simp]
theorem eventQueryDepth_tensorQubits {m n : Nat}
    (focus : Resource.Event .quantum) (left : UnitaryCircuit (Qubits m))
    (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).eventQueryDepth focus =
      max (left.eventQueryDepth focus) (right.eventQueryDepth focus) := rfl

@[simp]
theorem resourcesFromEventDepth_tensorQubits {m n : Nat}
    (left : UnitaryCircuit (Qubits m)) (right : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensorQubits left right layout).resourcesFromEventDepth =
      left.resourcesFromEventDepth + right.resourcesFromEventDepth := rfl





@[simp]
theorem controlQubitsAt_matrix {n : Nat} (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout activationValue).matrix =
      UnitaryOperator.reindex (prodEquiv (m := 1) (n := n))
        (UnitaryOperator.controlled (Qubits 1) activationValue body.matrix) :=
  rfl

@[simp]
theorem controlQubitsAt_eventTrace {n : Nat} (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout activationValue).eventTrace =
      body.eventTrace.map (fun event => event.controlForDimension 2) := rfl





@[simp]
theorem controlQubitsAt_eventCost {n : Nat} (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout activationValue).eventCost =
      ResourcePool.controlForDimension 2 body.eventCost :=
  rfl

@[simp]
theorem controlQubitsAt_eventDepth {n : Nat} (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout activationValue).eventDepth =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension 2 body.eventDepth) :=
  rfl

theorem evaluatedEventDepth_controlQubitsAt {n : Nat}
    (assign : Resource.Event .quantum → Nat) (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout activationValue).evaluatedEventDepth
        assign =
      DepthExpr.costEval
        (fun event => assign (event.controlForDimension 2)) body.eventDepth := by
  simpa [controlQubitsAt_eventDepth, evaluatedEventDepth] using
    DepthExpr.depthEval_controlEventsForDimension assign 2 body.eventDepth

theorem resourcesFromEventDepth_controlQubitsAt {n : Nat}
    (controlSystemIdx : List Nat) (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout
        activationValue).resourcesFromEventDepth =
      ResourcePool.controlForDimension 2 body.resourcesFromEventDepth := by
  simpa [controlQubitsAt_eventDepth, resourcesFromEventDepth] using
    DepthExpr.resourcesFromControlEventsForDimension 2 body.eventDepth

theorem count_controlQubitsAt_eventCost {n : Nat}
    (focus : Resource.Event .quantum) (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    ResourcePool.count (focus.controlForDimension 2)
        (controlQubitsAt controlSystemIdx body layout activationValue).eventCost =
      ResourcePool.count focus body.eventCost := by
  rw [controlQubitsAt_eventCost]
  exact ResourcePool.count_controlForDimension 2 focus body.eventCost

@[simp]
theorem eventQueryDepth_controlQubitsAt {n : Nat}
    (focus : Resource.Event .quantum) (controlSystemIdx : List Nat)
    (body : UnitaryCircuit (Qubits n))
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : Fin 2) :
    (controlQubitsAt controlSystemIdx body layout activationValue).eventQueryDepth
        (focus.controlForDimension 2) =
      DepthExpr.costEval (DepthExpr.indicator focus) body.eventDepth := by
  change DepthExpr.queryDepthEval (focus.controlForDimension 2)
      (controlQubitsAt controlSystemIdx body layout activationValue).eventDepth =
    DepthExpr.costEval (DepthExpr.indicator focus) body.eventDepth
  rw [controlQubitsAt_eventDepth]
  simpa [DepthExpr.queryDepthEval] using
    DepthExpr.queryDepthEval_controlEventsForDimension focus 2 body.eventDepth

@[simp]
theorem relabel_physical_idx {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).physical_idx = newPhysicalIdx :=
  rfl

theorem relabel_physical_idx_eq_map {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).physical_idx =
      circuit.physical_idx.map relabeling.toFun :=
  relabeling.map_layout.symm

theorem relabel_physical_idx_nodup {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).physical_idx.Nodup :=
  relabeling.new_nodup

@[simp]
theorem relabel_matrix {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    ((circuit.relabel relabeling).matrix : HilbertOperator R) =
      (circuit.matrix : HilbertOperator R) := by
  simp [relabel, matrix]

@[simp]
theorem relabel_eventTrace {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).eventTrace = circuit.eventTrace := by
  simp [relabel, eventTrace]





@[simp]
theorem relabel_eventCost {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).eventCost = circuit.eventCost := by
  simp [relabel, eventCost]

@[simp]
theorem relabel_eventDepth {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).eventDepth = circuit.eventDepth := by
  simp [relabel, eventDepth]

@[simp]
theorem evaluatedEventDepth_relabel {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx)
    (assign : Resource.Event .quantum → Nat) :
    (circuit.relabel relabeling).evaluatedEventDepth assign =
      circuit.evaluatedEventDepth assign := by
  simp [evaluatedEventDepth]

@[simp]
theorem eventQueryDepth_relabel {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx)
    (focus : Resource.Event .quantum) :
    (circuit.relabel relabeling).eventQueryDepth focus =
      circuit.eventQueryDepth focus := by
  simp [eventQueryDepth]

theorem resourcesFromEventDepth_relabel {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx) :
    (circuit.relabel relabeling).resourcesFromEventDepth =
      circuit.resourcesFromEventDepth := by
  simp [resourcesFromEventDepth]

@[simp]
theorem relabel_applyVec {R : Register} (circuit : UnitaryCircuit R)
    {newPhysicalIdx : List Nat}
    (relabeling : PhysicalLayout.Relabeling circuit.physical_idx newPhysicalIdx)
    (state : HilbertVector R) :
    (circuit.relabel relabeling).applyVec state = circuit.applyVec state := by
  change HilbertOperator.applyVec
      ((circuit.relabel relabeling).matrix : HilbertOperator R) state =
    HilbertOperator.applyVec (circuit.matrix : HilbertOperator R) state
  rw [relabel_matrix]


@[simp]
theorem controlAt_physical_idx {R : Register} (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).physical_idx =
      controlSystemIdx ++ body.physical_idx := rfl

/-- Checked circuit control always produces a duplicate-free merged physical
layout. -/
theorem controlAt_physical_idx_nodup {R : Register} (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).physical_idx.Nodup :=
  layout.merged_nodup

@[simp]
theorem controlAt_matrix {R : Register} (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).matrix =
      UnitaryOperator.controlled control activationValue body.matrix := rfl

@[simp]
theorem controlAt_eventTrace {R : Register} (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).eventTrace =
      body.eventTrace.map (fun event =>
        event.controlForDimension (Fintype.card control.Index)) := rfl





@[simp]
theorem controlAt_eventCost {R : Register} (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).eventCost =
      ResourcePool.controlForDimension
        (Fintype.card control.Index) body.eventCost := rfl

@[simp]
theorem controlAt_eventDepth {R : Register} (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).eventDepth =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) body.eventDepth) := rfl

theorem count_controlAt_eventCost {R : Register}
    (focus : Resource.Event .quantum) (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    ResourcePool.count
        (focus.controlForDimension (Fintype.card control.Index))
        (controlAt control controlSystemIdx body layout activationValue).eventCost =
      ResourcePool.count focus body.eventCost := by
  rw [controlAt_eventCost]
  exact ResourcePool.count_controlForDimension
    (Fintype.card control.Index) focus body.eventCost

theorem evaluatedEventDepth_controlAt {R : Register}
    (assign : Resource.Event .quantum → Nat) (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).evaluatedEventDepth
        assign =
      DepthExpr.costEval (fun event =>
        assign (event.controlForDimension (Fintype.card control.Index))) body.eventDepth := by
  change DepthExpr.depthEval assign
      (.controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) body.eventDepth)) =
    DepthExpr.costEval
      (fun event => assign
        (event.controlForDimension (Fintype.card control.Index))) body.eventDepth
  simpa using DepthExpr.depthEval_controlEventsForDimension
    assign (Fintype.card control.Index) body.eventDepth

@[simp]
theorem eventQueryDepth_controlAt {R : Register}
    (focus : Resource.Event .quantum) (control : Register)
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).eventQueryDepth
        (focus.controlForDimension (Fintype.card control.Index)) =
      DepthExpr.costEval (DepthExpr.indicator focus) body.eventDepth := by
  change DepthExpr.queryDepthEval
      (focus.controlForDimension (Fintype.card control.Index))
      (.controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) body.eventDepth)) =
    DepthExpr.costEval (DepthExpr.indicator focus) body.eventDepth
  simpa [DepthExpr.queryDepthEval] using
    DepthExpr.queryDepthEval_controlEventsForDimension
      focus (Fintype.card control.Index) body.eventDepth

theorem resourcesFromEventDepth_controlAt {R : Register}
    (control : Register) (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index) :
    (controlAt control controlSystemIdx body layout activationValue).resourcesFromEventDepth =
      ResourcePool.controlForDimension (Fintype.card control.Index)
        body.resourcesFromEventDepth := by
  change DepthExpr.costEval (fun event => ResourcePool.singleton event)
      (.controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) body.eventDepth)) =
    ResourcePool.controlForDimension (Fintype.card control.Index)
      (DepthExpr.costEval (fun event => ResourcePool.singleton event) body.eventDepth)
  simpa using DepthExpr.resourcesFromControlEventsForDimension
    (Fintype.card control.Index) body.eventDepth





@[simp]
theorem control_matrix {R : Register} (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout activationValue).matrix =
      UnitaryOperator.controlled control activationValue body.matrix := rfl

@[simp]
theorem control_eventTrace {R : Register} (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout
        activationValue).eventTrace =
      body.eventTrace.map (fun event =>
        event.controlForDimension (Fintype.card control.Index)) := rfl





@[simp]
theorem control_eventCost {R : Register} (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout activationValue).eventCost =
      ResourcePool.controlForDimension
        (Fintype.card control.Index) body.eventCost := rfl

@[simp]
theorem control_eventDepth {R : Register} (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout activationValue).eventDepth =
      .controlled "circuit-control"
        (DepthExpr.controlEventsForDimension
          (Fintype.card control.Index) body.eventDepth) := rfl

theorem count_control_eventCost {R : Register}
    (focus : Resource.Event .quantum) (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    ResourcePool.count
        (focus.controlForDimension (Fintype.card control.Index))
        (UnitaryCircuit.control control controlSystemIdx body layout activationValue).eventCost =
      ResourcePool.count focus body.eventCost := by
  simp [UnitaryCircuit.control]

@[simp]
theorem eventQueryDepth_control {R : Register}
    (focus : Resource.Event .quantum) (control : Register) [LE control.Index]
    [OrderTop control.Index] (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout activationValue).eventQueryDepth
        (focus.controlForDimension (Fintype.card control.Index)) =
      DepthExpr.costEval (DepthExpr.indicator focus) body.eventDepth := by
  simp [UnitaryCircuit.control]

theorem evaluatedEventDepth_control {R : Register}
    (assign : Resource.Event .quantum → Nat)
    (control : Register) [LE control.Index] [OrderTop control.Index]
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout
        activationValue).evaluatedEventDepth assign =
      DepthExpr.costEval (fun event =>
        assign (event.controlForDimension (Fintype.card control.Index))) body.eventDepth := by
  exact evaluatedEventDepth_controlAt assign control controlSystemIdx body layout
    activationValue

theorem resourcesFromEventDepth_control {R : Register}
    (control : Register) [LE control.Index] [OrderTop control.Index]
    (controlSystemIdx : List Nat) (body : UnitaryCircuit R)
    (layout : PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx)
    (activationValue : control.Index := ⊤) :
    (UnitaryCircuit.control control controlSystemIdx body layout
        activationValue).resourcesFromEventDepth =
      ResourcePool.controlForDimension (Fintype.card control.Index)
        body.resourcesFromEventDepth := by
  exact resourcesFromEventDepth_controlAt control controlSystemIdx body layout
    activationValue






@[simp]
theorem tensor_physical_idx {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).physical_idx = left.physical_idx ++ right.physical_idx :=
  rfl

theorem tensor_physical_idx_nodup {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).physical_idx.Nodup :=
  layout.merged_nodup

@[simp]
theorem tensor_matrix {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    ((tensor left right layout).matrix : HilbertOperator (Register.prod R S)) =
      (left.matrix : HilbertOperator R) ⊗ₖ (right.matrix : HilbertOperator S) :=
  rfl

@[simp]
theorem tensor_eventTrace {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).eventTrace =
      left.eventTrace ++ right.eventTrace := rfl





@[simp]
theorem tensor_eventCost {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).eventCost = left.eventCost + right.eventCost := rfl

@[simp]
theorem tensor_eventDepth {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).eventDepth =
      .tensor left.eventDepth right.eventDepth := rfl

@[simp]
theorem evaluatedEventDepth_tensor {R S : Register}
    (assign : Resource.Event .quantum → Nat) (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).evaluatedEventDepth assign =
      max (left.evaluatedEventDepth assign) (right.evaluatedEventDepth assign) := rfl

@[simp]
theorem eventQueryDepth_tensor {R S : Register}
    (focus : Resource.Event .quantum) (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).eventQueryDepth focus =
      max (left.eventQueryDepth focus) (right.eventQueryDepth focus) := rfl

@[simp]
theorem resourcesFromEventDepth_tensor {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx) :
    (tensor left right layout).resourcesFromEventDepth =
      left.resourcesFromEventDepth + right.resourcesFromEventDepth := rfl






@[simp]
theorem tensorRelabeled_physical_idx {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling layout).physical_idx =
      leftPhysical ++ rightPhysical :=
  rfl

theorem tensorRelabeled_physical_idx_nodup {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling layout).physical_idx.Nodup :=
  layout.merged_nodup

private theorem tensorRelabeled_layout {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    PhysicalLayout.DisjointMerge
      (left.relabel leftRelabeling).physical_idx
      (right.relabel rightRelabeling).physical_idx := by
  simpa only [relabel_physical_idx] using layout

@[simp]
theorem tensorRelabeled_matrix {R S : Register} (left : UnitaryCircuit R) (right : UnitaryCircuit S)
    {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    ((tensorRelabeled left right leftRelabeling rightRelabeling layout).matrix :
        HilbertOperator (Register.prod R S)) =
      (left.matrix : HilbertOperator R) ⊗ₖ (right.matrix : HilbertOperator S) := by
  simpa only [tensorRelabeled, relabel_matrix] using
    (tensor_matrix (left.relabel leftRelabeling) (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

@[simp]
theorem tensorRelabeled_eventTrace {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling layout).eventTrace =
      left.eventTrace ++ right.eventTrace := by
  simpa only [tensorRelabeled, relabel_eventTrace] using
    (tensor_eventTrace (left.relabel leftRelabeling) (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

@[simp]
theorem tensorRelabeled_eventCost {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling layout).eventCost =
      left.eventCost + right.eventCost := by
  simpa only [tensorRelabeled, relabel_eventCost] using
    (tensor_eventCost (left.relabel leftRelabeling) (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

@[simp]
theorem tensorRelabeled_eventDepth {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling layout).eventDepth =
      .tensor left.eventDepth right.eventDepth := by
  simpa only [tensorRelabeled, relabel_eventDepth] using
    (tensor_eventDepth (left.relabel leftRelabeling) (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

@[simp]
theorem evaluatedEventDepth_tensorRelabeled {R S : Register}
    (assign : Resource.Event .quantum → Nat)
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling
        layout).evaluatedEventDepth assign =
      max (left.evaluatedEventDepth assign) (right.evaluatedEventDepth assign) := by
  simpa only [tensorRelabeled, evaluatedEventDepth_relabel] using
    (evaluatedEventDepth_tensor assign (left.relabel leftRelabeling)
      (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

@[simp]
theorem eventQueryDepth_tensorRelabeled {R S : Register}
    (focus : Resource.Event .quantum)
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling
        layout).eventQueryDepth focus =
      max (left.eventQueryDepth focus) (right.eventQueryDepth focus) := by
  simpa only [tensorRelabeled, eventQueryDepth_relabel] using
    (eventQueryDepth_tensor focus (left.relabel leftRelabeling)
      (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

theorem resourcesFromEventDepth_tensorRelabeled {R S : Register}
    (left : UnitaryCircuit R) (right : UnitaryCircuit S) {leftPhysical rightPhysical : List Nat}
    (leftRelabeling : PhysicalLayout.Relabeling left.physical_idx leftPhysical)
    (rightRelabeling : PhysicalLayout.Relabeling right.physical_idx rightPhysical)
    (layout : PhysicalLayout.DisjointMerge leftPhysical rightPhysical) :
    (tensorRelabeled left right leftRelabeling rightRelabeling
        layout).resourcesFromEventDepth =
      left.resourcesFromEventDepth + right.resourcesFromEventDepth := by
  simpa only [tensorRelabeled, resourcesFromEventDepth_relabel] using
    (resourcesFromEventDepth_tensor (left.relabel leftRelabeling)
      (right.relabel rightRelabeling)
      (tensorRelabeled_layout left right leftRelabeling rightRelabeling layout))

/-- Two unit-depth atoms on disjoint layouts have max-plus depth one even
though their linear resource cost contains two occurrences. -/
example (left right : UnitaryCircuit (Qubits 1))
    (layout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx)
    (leftEvent rightEvent : Resource.Event .quantum)
    (leftAtom : left.eventDepth = .atom leftEvent)
    (rightAtom : right.eventDepth = .atom rightEvent) :
    (tensor left right layout).evaluatedEventDepth (fun _ => 1) = 1 := by
  simp [evaluatedEventDepth, leftAtom, rightAtom]

/-- Adding one shared control to two disjoint atoms requires two sequential
layers, although the uncontrolled tensor has depth one. -/
example (left right : UnitaryCircuit (Qubits 1))
    (bodyLayout : PhysicalLayout.DisjointMerge left.physical_idx right.physical_idx)
    (controlLayout : PhysicalLayout.DisjointMerge [2]
      (tensor left right bodyLayout).physical_idx)
    (leftEvent rightEvent : Resource.Event .quantum)
    (leftAtom : left.eventDepth = .atom leftEvent)
    (rightAtom : right.eventDepth = .atom rightEvent) :
    (controlAt (Qubits 1) [2] (tensor left right bodyLayout) controlLayout
      (1 : Fin 2)).evaluatedEventDepth (fun _ => 1) = 2 := by
  rw [evaluatedEventDepth_controlAt]
  simp [leftAtom, rightAtom]

namespace ControlledSubroutineFixtures

private def label : Resource.SubroutineLabel :=
  { family := "fixture", name := "controlled-coordinate-regression", parameters := [3] }

private def baseEvent : Resource.Event .quantum :=
  .quantumSubroutine label.quantum

private def singleEvent : Resource.Event .quantum :=
  baseEvent.controlForDimension 2

private def nestedEvent : Resource.Event .quantum :=
  baseEvent.controlForDimensions [2, 3]

private def reversedNestedEvent : Resource.Event .quantum :=
  baseEvent.controlForDimensions [3, 2]

private def single (direct : UnitaryCircuit (Qubits 1))
    (layout : PhysicalLayout.DisjointMerge [1] direct.physical_idx) :
    UnitaryCircuit (Register.prod (Qubits 1) (Qubits 1)) :=
  controlAt (Qubits 1) [1] direct layout (1 : Fin 2)

private def qutrit : Register :=
  { Index := Fin 3, fintype := inferInstance, decEq := inferInstance }

private def nested (direct : UnitaryCircuit (Qubits 1))
    (qubitLayout : PhysicalLayout.DisjointMerge [1] direct.physical_idx)
    (qutritLayout : PhysicalLayout.DisjointMerge [2]
      (single direct qubitLayout).physical_idx) :
    UnitaryCircuit (Register.prod qutrit (Register.prod (Qubits 1) (Qubits 1))) :=
  controlAt qutrit [2] (single direct qubitLayout) qutritLayout (2 : Fin 3)

/-- Successive controls normalize from the base outward, while reversing two
different control dimensions remains a different capability. -/
example :
    singleEvent.controlForDimension 3 = nestedEvent ∧
      baseEvent ≠ singleEvent ∧ singleEvent ≠ nestedEvent ∧
      nestedEvent ≠ reversedNestedEvent := by
  decide

/-- Direct, singly controlled, and nested circuits each charge exactly their
own derived opaque-subroutine coordinate. -/
example (direct : UnitaryCircuit (Qubits 1))
    (qubitLayout : PhysicalLayout.DisjointMerge [1] direct.physical_idx)
    (qutritLayout : PhysicalLayout.DisjointMerge [2]
      (single direct qubitLayout).physical_idx)
    (directEventCost : direct.eventCost = ResourcePool.singleton baseEvent) :
    ResourcePool.count baseEvent direct.eventCost = 1 ∧
      ResourcePool.count singleEvent (single direct qubitLayout).eventCost = 1 ∧
      ResourcePool.count nestedEvent
        (nested direct qubitLayout qutritLayout).eventCost = 1 := by
  simp [single, nested, directEventCost, singleEvent, nestedEvent, qutrit]

/-- Query depth follows the exact derived coordinate: control never pools a
query back to the base, an intermediate layer, or a reversed nesting order. -/
example (direct : UnitaryCircuit (Qubits 1))
    (qubitLayout : PhysicalLayout.DisjointMerge [1] direct.physical_idx)
    (qutritLayout : PhysicalLayout.DisjointMerge [2]
      (single direct qubitLayout).physical_idx)
    (directEventDepth : direct.eventDepth = .atom baseEvent) :
    direct.eventQueryDepth baseEvent = 1 ∧
      direct.dagger.eventQueryDepth baseEvent = 1 ∧
      (single direct qubitLayout).eventQueryDepth baseEvent = 0 ∧
      (single direct qubitLayout).eventQueryDepth singleEvent = 1 ∧
      (nested direct qubitLayout qutritLayout).eventQueryDepth nestedEvent = 1 ∧
      (nested direct qubitLayout qutritLayout).eventQueryDepth baseEvent = 0 ∧
      (nested direct qubitLayout qutritLayout).eventQueryDepth singleEvent = 0 ∧
      (nested direct qubitLayout qutritLayout).eventQueryDepth
        reversedNestedEvent = 0 := by
  have daggerEventDepth :
      direct.dagger.eventDepth = DepthExpr.inverse (.atom baseEvent) := by
    change DepthExpr.inverse direct.eventDepth =
      DepthExpr.inverse (.atom baseEvent)
    rw [directEventDepth]
  have singleEventDepth :
      (single direct qubitLayout).eventDepth =
        .controlled "circuit-control" (.atom singleEvent) := by
    simp [single, directEventDepth, singleEvent,
      Resource.Event.controlForDimension,
      DepthExpr.controlEventsForDimension,
      DepthExpr.controlEventsForDimensions]
  have nestedEventDepth :
      (nested direct qubitLayout qutritLayout).eventDepth =
        .controlled "circuit-control"
          (.controlled "circuit-control" (.atom nestedEvent)) := by
    simp [nested, singleEventDepth, singleEvent, nestedEvent, qutrit,
      Resource.Event.controlForDimension,
      DepthExpr.controlEventsForDimension,
      DepthExpr.controlEventsForDimensions]
  simp only [eventQueryDepth, directEventDepth, daggerEventDepth,
    singleEventDepth, nestedEventDepth, baseEvent, singleEvent, nestedEvent,
    reversedNestedEvent, label, DepthExpr.queryDepthEval,
    DepthExpr.depthEval_atom, DepthExpr.depthEval_inverse,
    DepthExpr.depthEval_controlled, DepthExpr.indicator]
  decide

/-- Base, singly controlled, and nested budgets are independent strict
coordinates in both directions. -/
example (direct : UnitaryCircuit (Qubits 1))
    (qubitLayout : PhysicalLayout.DisjointMerge [1] direct.physical_idx)
    (qutritLayout : PhysicalLayout.DisjointMerge [2]
      (single direct qubitLayout).physical_idx)
    (directEventCost : direct.eventCost = ResourcePool.singleton baseEvent) :
    ¬(single direct qubitLayout).eventCost ≤ direct.eventCost ∧
      ¬direct.eventCost ≤ (single direct qubitLayout).eventCost ∧
      ¬(nested direct qubitLayout qutritLayout).eventCost ≤
        (single direct qubitLayout).eventCost ∧
      ¬(single direct qubitLayout).eventCost ≤
        (nested direct qubitLayout qutritLayout).eventCost := by
  have singleEventCost :
      (single direct qubitLayout).eventCost =
        ResourcePool.singleton singleEvent := by
    simp [single, directEventCost, singleEvent]
  have nestedEventCost :
      (nested direct qubitLayout qutritLayout).eventCost =
        ResourcePool.singleton nestedEvent := by
    simp [nested, singleEventCost, singleEvent, nestedEvent, qutrit]
  rw [directEventCost, singleEventCost, nestedEventCost]
  decide

end ControlledSubroutineFixtures

/-- A sealed leaf on physical system zero cannot be represented by a
circuit advertising the empty physical layout. -/
theorem leaf_on_zero_cannot_use_empty_layout
    (leaf : UnitaryLeaf (Qubits 1)) (usesZero : 0 ∈ leaf.systemIdx) :
    ¬ ∃ circuit : UnitaryCircuit (Qubits 1),
      circuit.physical_idx = [] ∧ circuit.sequence = .leaf leaf := by
  rintro ⟨circuit, hphysical, hsequence⟩
  have hcontained := circuit.sequence_atoms_contained
  rw [hphysical, hsequence] at hcontained
  have himpossible : 0 ∈ ([] : List Nat) := hcontained.2 usesZero
  simp at himpossible

/-- A sealed leaf with duplicate placement cannot hide behind a
duplicate-free singleton circuit layout. -/
theorem duplicate_leaf_cannot_use_singleton_layout
    (leaf : UnitaryLeaf (Qubits 1))
    (duplicateSystemIdx : ¬leaf.systemIdx.Nodup) :
    ¬ ∃ circuit : UnitaryCircuit (Qubits 1),
      circuit.physical_idx = [0] ∧ circuit.sequence = .leaf leaf := by
  rintro ⟨circuit, hphysical, hsequence⟩
  have hcontained := circuit.sequence_atoms_contained
  rw [hphysical, hsequence] at hcontained
  exact duplicateSystemIdx hcontained.1

/-- A control on physical system zero cannot be merged with a body already
using physical system zero. -/
theorem singleton_zero_not_disjoint_merge_self :
    ¬ PhysicalLayout.DisjointMerge [0] [0] := by
  intro layout
  simpa using layout.disjoint

/-- Compile-time regression: circuit control consumes a disjoint-layout
certificate before it accepts the activation value. -/
example :
    ∀ {R : Register} (control : Register) (controlSystemIdx : List Nat)
        (body : UnitaryCircuit R),
      PhysicalLayout.DisjointMerge controlSystemIdx body.physical_idx →
        control.Index → UnitaryCircuit (Register.prod control R) :=
  fun {_} control controlSystemIdx body layout activationValue =>
    UnitaryCircuit.controlAt control controlSystemIdx body layout activationValue

end

end UnitaryCircuit

end QuantumAlg

end
