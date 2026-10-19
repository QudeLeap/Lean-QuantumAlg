/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.BinaryLabelEncoding
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Addressed reversible qubit operators

The common X/CNOT/Toffoli basis actions, physical wire selections and unitary
operators are independent of circuit syntax and its native resource model.
-/

section

namespace QuantumAlg

noncomputable section

/-- Wire-addressed declarations for the common reversible qubit primitives. -/
public inductive QubitPrimitive (n : Nat) where
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
public def applyLabel {n : Nat} : QubitPrimitive n → Fin (2 ^ n) → Fin (2 ^ n)
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
lemma perm_apply {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) : primitive.perm label = primitive.applyLabel label := by
  cases primitive <;> simp [perm, applyLabel]

/-- Physical wires touched by one primitive declaration. -/
def systemIdx {n : Nat} : QubitPrimitive n → List Nat
  | .x target => [target.val]
  | .cnot control target _ => [control.val, target.val]
  | .toffoli controlA controlB target _ _ _ =>
      [controlA.val, controlB.val, target.val]

/-- Primitive construction witnesses guarantee a duplicate-free footprint. -/
lemma systemIdx_nodup {n : Nat} (primitive : QubitPrimitive n) :
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
lemma systemIdx_subset_range {n : Nat} (primitive : QubitPrimitive n) :
    primitive.systemIdx ⊆ List.range n := by
  cases primitive with
  | x target => simp [systemIdx, target.isLt]
  | cnot control target hct =>
      simp [systemIdx, control.isLt, target.isLt]
  | toffoli controlA controlB target hab ha hb =>
      simp [systemIdx, controlA.isLt, controlB.isLt, target.isLt]

/-- Every primitive declaration is self-inverse on basis labels. -/
lemma applyLabel_applyLabel {n : Nat} (primitive : QubitPrimitive n)
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

/-- Canonical unitary operator of one addressed primitive declaration. -/
public def operator {n : Nat} (primitive : QubitPrimitive n) :
    UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofPerm primitive.perm.symm

@[simp]
public lemma operator_apply_ket {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) :
    primitive.operator.apply (NormalizedVector.ket label) =
      NormalizedVector.ket (primitive.applyLabel label) := by
  unfold operator
  rw [UnitaryOperator.ofPerm_apply_ket]
  change NormalizedVector.ket (R := Qubits n) (primitive.perm label) = _
  rw [perm_apply]

end QubitPrimitive

end

end QuantumAlg

end
