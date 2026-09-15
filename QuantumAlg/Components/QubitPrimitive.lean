/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Addressed reversible qubit primitives

This module owns the common Components-level declarations of addressed
X/CNOT/Toffoli gates.  Each declaration fixes its operator, placement, strict
event label, and direct Core `UnitaryCircuit` constructor.  It does not certify or
classify arbitrary circuits as belonging to a global gate language.
-/

section

namespace QuantumAlg

noncomputable section

/-- Wire-addressed declarations for the common reversible qubit primitives. -/
inductive QubitPrimitive (n : Nat) where
  /-- Flip one addressed qubit. -/
  | x (target : Fin n)
  /-- Flip a target qubit when one distinct control qubit is set. -/
  | cnot (control target : Fin n) (hct : control ≠ target)
  /-- Flip a target qubit when two pairwise-distinct controls are set. -/
  | toffoli (controlA controlB target : Fin n)
      (hab : controlA ≠ controlB) (ha : controlA ≠ target)
      (hb : controlB ≠ target)

namespace QubitPrimitive

/-- Classical computational-basis action of one primitive declaration. -/
def applyLabel {n : Nat} : QubitPrimitive n → Fin (2 ^ n) → Fin (2 ^ n)
  | .x target, label => WireAddress.flipBit target label
  | .cnot control target _hct, label => WireAddress.cnotMap control target label
  | .toffoli controlA controlB target _hab _ha _hb, label =>
      WireAddress.toffoliMap controlA controlB target label

/-- Certified basis permutation of one primitive declaration. -/
def perm {n : Nat} : QubitPrimitive n → Equiv.Perm (Fin (2 ^ n))
  | .x target => WireAddress.xPerm target
  | .cnot control target hct => WireAddress.cnotPerm control target hct
  | .toffoli controlA controlB target hab ha hb =>
      WireAddress.toffoliPerm controlA controlB target hab ha hb

@[simp]
theorem perm_apply {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) : primitive.perm label = primitive.applyLabel label := by
  cases primitive <;> rfl

/-- Physical wires touched by one primitive declaration. -/
def systemIdx {n : Nat} : QubitPrimitive n → List Nat
  | .x target => [target.val]
  | .cnot control target _ => [control.val, target.val]
  | .toffoli controlA controlB target _ _ _ =>
      [controlA.val, controlB.val, target.val]

/-- Strict gate coordinate contributed by one primitive declaration. -/
def gateLabel {n : Nat} : QubitPrimitive n → Resource.GateLabel
  | .x _ => .builtin "x"
  | .cnot _ _ _ => .builtin "cnot"
  | .toffoli _ _ _ _ _ _ => .builtin "toffoli"

/-- Strict execution event contributed by one primitive declaration. -/
def event {n : Nat} (primitive : QubitPrimitive n) : Resource.Event .quantum :=
  .gate primitive.gateLabel

/-- Primitive construction witnesses guarantee a duplicate-free footprint. -/
theorem systemIdx_nodup {n : Nat} (primitive : QubitPrimitive n) :
    primitive.systemIdx.Nodup := by
  cases primitive with
  | x target => simp [systemIdx]
  | cnot control target hct =>
      have hval : control.val ≠ target.val := fun h => hct (Fin.ext h)
      simp [systemIdx, hval]
  | toffoli controlA controlB target hab ha hb =>
      have habv : controlA.val ≠ controlB.val := fun h => hab (Fin.ext h)
      have hav : controlA.val ≠ target.val := fun h => ha (Fin.ext h)
      have hbv : controlB.val ≠ target.val := fun h => hb (Fin.ext h)
      simp [systemIdx, habv, hav, hbv]

/-- Every addressed primitive wire lies in the canonical `n`-qubit range. -/
theorem systemIdx_subset_range {n : Nat} (primitive : QubitPrimitive n) :
    primitive.systemIdx ⊆ List.range n := by
  cases primitive with
  | x target => simp [systemIdx, target.isLt]
  | cnot control target hct =>
      simp [systemIdx, control.isLt, target.isLt]
  | toffoli controlA controlB target hab ha hb =>
      simp [systemIdx, controlA.isLt, controlB.isLt, target.isLt]

/-- Every primitive declaration is self-inverse on basis labels. -/
theorem applyLabel_applyLabel {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) :
    primitive.applyLabel (primitive.applyLabel label) = label := by
  cases primitive with
  | x target => exact WireAddress.flipBit_flipBit target label
  | cnot control target hct => exact WireAddress.cnotMap_cnotMap hct label
  | toffoli controlA controlB target _hab ha hb =>
      exact WireAddress.toffoliMap_toffoliMap ha hb label

/-- A primitive is disjoint from a wire when it neither reads nor writes it. -/
def wireDisjoint {n : Nat} (observed : Fin n) : QubitPrimitive n → Prop
  | .x target => target ≠ observed
  | .cnot control target _ => control ≠ observed ∧ target ≠ observed
  | .toffoli controlA controlB target _ _ _ =>
      controlA ≠ observed ∧ controlB ≠ observed ∧ target ≠ observed

/-- Canonical unitary operator owned by the addressed primitive family. -/
def qubitPrimitiveOperator {n : Nat} (primitive : QubitPrimitive n) :
    UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofPerm primitive.perm.symm

/-- Canonical unitary operator of one addressed primitive declaration. -/
def operator {n : Nat} (primitive : QubitPrimitive n) :
    UnitaryOperator (Qubits n) :=
  qubitPrimitiveOperator primitive

/-- Sealed primitive declaration at a caller-supplied physical placement. -/
def qubitPrimitiveLeafAt {n : Nat} (primitive : QubitPrimitive n)
    (systemIdx : List Nat) : UnitaryLeaf (Qubits n) :=
  UnitaryLeaf.gate (QubitPrimitive.gateLabel primitive) systemIdx
    (qubitPrimitiveOperator primitive)

/-- Sealed execution leaf of one addressed primitive declaration. -/
def leaf {n : Nat} (primitive : QubitPrimitive n) :
    UnitaryLeaf (Qubits n) :=
  qubitPrimitiveLeafAt primitive primitive.systemIdx

@[simp]
theorem leaf_operator {n : Nat} (primitive : QubitPrimitive n) :
    primitive.leaf.operator = primitive.operator :=
  rfl

@[simp]
theorem leaf_systemIdx {n : Nat} (primitive : QubitPrimitive n) :
    primitive.leaf.systemIdx = primitive.systemIdx :=
  rfl

@[simp]
theorem leaf_event {n : Nat} (primitive : QubitPrimitive n) :
    primitive.leaf.event = primitive.event :=
  rfl



@[simp]
theorem operator_apply_ket {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) :
    primitive.operator.apply (NormalizedVector.ket label) =
      NormalizedVector.ket (primitive.applyLabel label) := by
  unfold operator qubitPrimitiveOperator
  rw [UnitaryOperator.ofPerm_apply_ket]
  change NormalizedVector.ket (R := Qubits n) (primitive.perm label) = _
  rw [perm_apply]

/-- Direct Core circuit for one addressed primitive declaration. -/
def circuit {n : Nat} (primitive : QubitPrimitive n) : UnitaryCircuit (Qubits n) :=
  UnitaryCircuit.ofLeaf primitive.leaf primitive.systemIdx_nodup

/-- The circuit trace is derived from the same sealed primitive event. -/
@[simp] theorem circuit_eventTrace {n : Nat} (primitive : QubitPrimitive n) :
    primitive.circuit.eventTrace = [primitive.event] :=
  rfl

/-- The circuit event pool contains exactly the sealed primitive event. -/
@[simp] theorem circuit_eventCost {n : Nat} (primitive : QubitPrimitive n) :
    primitive.circuit.eventCost = ResourcePool.singleton primitive.event :=
  rfl

/-- The circuit event critical path contains exactly the sealed primitive event. -/
@[simp] theorem circuit_eventDepth {n : Nat} (primitive : QubitPrimitive n) :
    primitive.circuit.eventDepth = .atom primitive.event :=
  rfl

/-- One primitive contributes exactly one occurrence of its literal event. -/
theorem circuit_eventCount {n : Nat} (primitive : QubitPrimitive n) :
    ResourcePool.count primitive.event primitive.circuit.eventCost = 1 := by
  rw [circuit_eventCost, ResourcePool.count_singleton_self]

/-- No distinct event coordinate is charged by a primitive circuit. -/
theorem circuit_eventCount_of_ne {n : Nat} (primitive : QubitPrimitive n)
    (focus : Resource.Event .quantum) (hne : focus ≠ primitive.event) :
    ResourcePool.count focus primitive.circuit.eventCost = 0 := by
  rw [circuit_eventCost]
  exact ResourcePool.count_singleton_of_ne hne 1

/-- Linearizing the primitive event path reproduces its event pool. -/
theorem circuit_resourcesFromEventDepth {n : Nat}
    (primitive : QubitPrimitive n) :
    primitive.circuit.resourcesFromEventDepth = primitive.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost primitive.circuit

@[simp]
theorem circuit_physical_idx {n : Nat} (primitive : QubitPrimitive n) :
    primitive.circuit.physical_idx = primitive.systemIdx :=
  rfl

@[simp]
theorem circuit_applyNormalized_ket {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) :
    primitive.circuit.applyNormalized (NormalizedVector.ket label) =
      NormalizedVector.ket (primitive.applyLabel label) := by
  exact primitive.operator_apply_ket label

end QubitPrimitive

end

end QuantumAlg

end
