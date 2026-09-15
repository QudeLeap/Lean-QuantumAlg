/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# Actual-circuit register lifting

These operations lift actual circuits across product-register layouts.  They
use Core tensor, reindex, and physical relabeling constructors directly; no
gate-language certificate or inverse compilation path is introduced.
-/

section

namespace QuantumAlg

noncomputable section

namespace UnitaryCircuit

/-- Extend an actual circuit with an untouched right qubit register. -/
def prodLeft {m n : Nat} (program : UnitaryCircuit (Qubits m)) :
    UnitaryCircuit (Qubits (m + n)) :=
  UnitaryCircuit.tensorQubits program
    (UnitaryCircuit.identity (Qubits n) [] List.nodup_nil)
    { left_nodup := program.physical_idx_nodup
      right_nodup := List.nodup_nil
      disjoint := by
        change program.physical_idx.Disjoint []
        exact List.disjoint_nil_right program.physical_idx }

/-- Extend an actual circuit with an untouched left qubit register.  The body
footprint is shifted past that register. -/
def prodRight {m n : Nat} (program : UnitaryCircuit (Qubits n)) :
    UnitaryCircuit (Qubits (m + n)) :=
  UnitaryCircuit.tensorQubits
    (UnitaryCircuit.identity (Qubits m) [] List.nodup_nil)
    (UnitaryCircuit.shiftPhysicalIdx m program)
    { left_nodup := List.nodup_nil
      right_nodup := (UnitaryCircuit.shiftPhysicalIdx m program).physical_idx_nodup
      disjoint := by
        change [].Disjoint (List.map (fun index => m + index) program.physical_idx)
        exact List.disjoint_nil_left
          (List.map (fun index => m + index) program.physical_idx) }

/-- Extending a circuit with an untouched right register preserves canonical
physical-range containment. -/
theorem prodLeft_physical_idx_subset_range {m n : Nat}
    (program : UnitaryCircuit (Qubits m))
    (contained : program.physical_idx ⊆ List.range m) :
    (prodLeft (n := n) program).physical_idx ⊆ List.range (m + n) := by
  unfold prodLeft
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · intro index hindex
    have indexLt : index < m := List.mem_range.mp (contained hindex)
    exact List.mem_range.mpr (Nat.lt_of_lt_of_le indexLt (Nat.le_add_right _ _))
  · simp [UnitaryCircuit.identity]

/-- Extending a circuit with an untouched left register preserves canonical
physical-range containment. -/
theorem prodRight_physical_idx_subset_range {m n : Nat}
    (program : UnitaryCircuit (Qubits n))
    (contained : program.physical_idx ⊆ List.range n) :
    (prodRight (m := m) program).physical_idx ⊆ List.range (m + n) := by
  unfold prodRight
  apply UnitaryCircuit.tensorQubits_physical_idx_subset
  · simp [UnitaryCircuit.identity]
  · exact UnitaryCircuit.shiftPhysicalIdx_physical_idx_subset_range m program contained

/-! Strict event accounting is the production API for circuit lifting. -/

@[simp] theorem prodLeft_eventTrace {m n : Nat}
    (program : UnitaryCircuit (Qubits m)) :
    (prodLeft (n := n) program).eventTrace = program.eventTrace := by
  simp [prodLeft]

@[simp] theorem prodRight_eventTrace {m n : Nat}
    (program : UnitaryCircuit (Qubits n)) :
    (prodRight (m := m) program).eventTrace = program.eventTrace := by
  simp [prodRight]









@[simp] theorem prodLeft_eventCost {m n : Nat}
    (program : UnitaryCircuit (Qubits m)) :
    (prodLeft (n := n) program).eventCost = program.eventCost := by
  simp [prodLeft]

@[simp] theorem prodRight_eventCost {m n : Nat}
    (program : UnitaryCircuit (Qubits n)) :
    (prodRight (m := m) program).eventCost = program.eventCost := by
  simp [prodRight]

/-- Extending a circuit with an untouched right register tensors its strict
event critical path with the empty right path. -/
@[simp] theorem prodLeft_eventDepth {m n : Nat}
    (program : UnitaryCircuit (Qubits m)) :
    (prodLeft (n := n) program).eventDepth = .tensor program.eventDepth .id := by
  rfl

/-- Extending a circuit with an untouched left register tensors its strict
event critical path with the empty left path. -/
@[simp] theorem prodRight_eventDepth {m n : Nat}
    (program : UnitaryCircuit (Qubits n)) :
    (prodRight (m := m) program).eventDepth = .tensor .id program.eventDepth := by
  simp [prodRight]

@[simp] theorem prodLeft_evaluatedEventDepth {m n : Nat}
    (assign : Resource.Event .quantum → Nat)
    (program : UnitaryCircuit (Qubits m)) :
    (prodLeft (n := n) program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  unfold evaluatedEventDepth
  rw [prodLeft_eventDepth]
  simp

@[simp] theorem prodRight_evaluatedEventDepth {m n : Nat}
    (assign : Resource.Event .quantum → Nat)
    (program : UnitaryCircuit (Qubits n)) :
    (prodRight (m := m) program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  unfold evaluatedEventDepth
  rw [prodRight_eventDepth]
  simp

@[simp] theorem prodLeft_eventQueryDepth {m n : Nat}
    (focus : Resource.Event .quantum) (program : UnitaryCircuit (Qubits m)) :
    (prodLeft (n := n) program).eventQueryDepth focus =
      program.eventQueryDepth focus := by
  unfold eventQueryDepth
  rw [prodLeft_eventDepth]
  simp [DepthExpr.queryDepthEval]

@[simp] theorem prodRight_eventQueryDepth {m n : Nat}
    (focus : Resource.Event .quantum) (program : UnitaryCircuit (Qubits n)) :
    (prodRight (m := m) program).eventQueryDepth focus =
      program.eventQueryDepth focus := by
  unfold eventQueryDepth
  rw [prodRight_eventDepth]
  simp [DepthExpr.queryDepthEval]

theorem prodLeft_resourcesFromEventDepth {m n : Nat}
    (program : UnitaryCircuit (Qubits m)) :
    (prodLeft (n := n) program).resourcesFromEventDepth =
      program.resourcesFromEventDepth := by
  simp [prodLeft]

theorem prodRight_resourcesFromEventDepth {m n : Nat}
    (program : UnitaryCircuit (Qubits n)) :
    (prodRight (m := m) program).resourcesFromEventDepth =
      program.resourcesFromEventDepth := by
  simp [prodRight]






/-- Logical basis permutation that moves an appended middle register between
the original left and right fields. -/
def insertMiddleIndexEquiv (leftWidth middleWidth rightWidth : Nat) :
    Fin (2 ^ ((leftWidth + rightWidth) + middleWidth)) ≃
      Fin (2 ^ ((leftWidth + middleWidth) + rightWidth)) where
  toFun label :=
    let sourceMiddle :=
      (prodEquiv (m := leftWidth + rightWidth) (n := middleWidth)).symm label
    let source :=
      (prodEquiv (m := leftWidth) (n := rightWidth)).symm sourceMiddle.1
    prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)
      (prodEquiv (m := leftWidth) (n := middleWidth)
        (source.1, sourceMiddle.2), source.2)
  invFun label :=
    let leftMiddleRight :=
      (prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)).symm label
    let leftMiddle :=
      (prodEquiv (m := leftWidth) (n := middleWidth)).symm
        leftMiddleRight.1
    prodEquiv (m := leftWidth + rightWidth) (n := middleWidth)
      (prodEquiv (m := leftWidth) (n := rightWidth)
        (leftMiddle.1, leftMiddleRight.2), leftMiddle.2)
  left_inv := by
    intro label
    simp
  right_inv := by
    intro label
    simp

/-- Shift every physical wire at or to the right of an insertion boundary. -/
def insertMiddlePhysicalIndex (leftWidth middleWidth index : Nat) : Nat :=
  if index < leftWidth then index else index + middleWidth

theorem insertMiddlePhysicalIndex_injective (leftWidth middleWidth : Nat) :
    Function.Injective (insertMiddlePhysicalIndex leftWidth middleWidth) := by
  intro left right h
  by_cases hleft : left < leftWidth <;>
    by_cases hright : right < leftWidth <;>
      simp [insertMiddlePhysicalIndex, hleft, hright] at h <;> omega

/-- Insert an untouched middle qubit register into an actual circuit over an
existing left/right product.  Logical basis transport and physical wire
shifting are both explicit Core circuit operations. -/
def insertMiddle {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    UnitaryCircuit (Qubits (leftWidth + middleWidth + rightWidth)) :=
  let extended := UnitaryCircuit.prodLeft (n := middleWidth) program
  let transported := UnitaryCircuit.reindex
    (insertMiddleIndexEquiv leftWidth middleWidth rightWidth) extended
  UnitaryCircuit.relabel transported
    { toFun := insertMiddlePhysicalIndex leftWidth middleWidth
      map_layout := rfl
      old_nodup := transported.physical_idx_nodup
      new_nodup := transported.physical_idx_nodup.map
        (insertMiddlePhysicalIndex_injective leftWidth middleWidth) }

/-- Inserting an untouched middle register maps a canonical source footprint
inside the correspondingly enlarged canonical carrier. -/
theorem insertMiddle_physical_idx_subset_range
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth)))
    (contained : program.physical_idx ⊆ List.range (leftWidth + rightWidth)) :
    (insertMiddle (middleWidth := middleWidth) program).physical_idx ⊆
      List.range (leftWidth + middleWidth + rightWidth) := by
  have extendedContained :
      (UnitaryCircuit.prodLeft (n := middleWidth) program).physical_idx ⊆
        List.range (leftWidth + rightWidth) := by
    unfold UnitaryCircuit.prodLeft
    apply UnitaryCircuit.tensorQubits_physical_idx_subset
    · exact contained
    · simp [UnitaryCircuit.identity]
  have transportedContained :
      (UnitaryCircuit.reindex
        (R := Qubits (leftWidth + rightWidth + middleWidth))
        (S := Qubits (leftWidth + middleWidth + rightWidth))
        (insertMiddleIndexEquiv leftWidth middleWidth rightWidth)
        (UnitaryCircuit.prodLeft (n := middleWidth) program)).physical_idx ⊆
        List.range (leftWidth + rightWidth) := by
    change (UnitaryCircuit.prodLeft (n := middleWidth) program).physical_idx ⊆
      List.range (leftWidth + rightWidth)
    exact extendedContained
  unfold insertMiddle
  dsimp
  intro index hindex
  rcases List.mem_map.mp hindex with ⟨source, hsource, rfl⟩
  have sourceLt : source < leftWidth + rightWidth :=
    List.mem_range.mp (transportedContained hsource)
  unfold insertMiddlePhysicalIndex
  by_cases hleft : source < leftWidth
  · simp [hleft]
    omega
  · simp [hleft]
    omega

@[simp] theorem insertMiddle_eventTrace
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    (insertMiddle (middleWidth := middleWidth) program).eventTrace =
      program.eventTrace := by
  simp [insertMiddle]





/-- Inserting an untouched middle register preserves the strict event pool. -/
@[simp] theorem insertMiddle_eventCost
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    (insertMiddle (middleWidth := middleWidth) program).eventCost =
      program.eventCost := by
  simp [insertMiddle]

/-- Inserting an untouched middle register tensors the strict event critical
path with the empty middle path. -/
@[simp] theorem insertMiddle_eventDepth
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    (insertMiddle (middleWidth := middleWidth) program).eventDepth =
      .tensor program.eventDepth .id := by
  simp [insertMiddle]

@[simp] theorem insertMiddle_evaluatedEventDepth
    {leftWidth middleWidth rightWidth : Nat}
    (assign : Resource.Event .quantum → Nat)
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    (insertMiddle (middleWidth := middleWidth) program).evaluatedEventDepth assign =
      program.evaluatedEventDepth assign := by
  unfold evaluatedEventDepth
  rw [insertMiddle_eventDepth]
  simp

@[simp] theorem insertMiddle_eventQueryDepth
    {leftWidth middleWidth rightWidth : Nat}
    (focus : Resource.Event .quantum)
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    (insertMiddle (middleWidth := middleWidth) program).eventQueryDepth focus =
      program.eventQueryDepth focus := by
  unfold eventQueryDepth
  rw [insertMiddle_eventDepth]
  simp [DepthExpr.queryDepthEval]

theorem insertMiddle_resourcesFromEventDepth
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth))) :
    (insertMiddle (middleWidth := middleWidth) program).resourcesFromEventDepth =
      program.resourcesFromEventDepth := by
  simp [insertMiddle]




end UnitaryCircuit

end

end QuantumAlg

end
