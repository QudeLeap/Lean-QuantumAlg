/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Primitives.Trotter.Native
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.BinaryLabelEncoding

/-!
# Addressed parity computation

The CNOT fan-in computes parity into one selected target, with one gate per
other support wire. It is an equivalent parity construction to the chain in
[WBA11, h2.arxiv2.tex:384-399], without a nearest-neighbor routing claim.
-/

namespace QuantumAlg.Trotter.PauliRotation

noncomputable section

/-- A CNOT control distinct from the parity target. -/
abbrev Control {n : ℕ} (target : Fin n) := {j : Fin n // j ≠ target}

/-- One addressed native CNOT with the canonical product-formula layout. -/
private def nativeCnot {n : ℕ} (t : Fin n) (c : Control t) : NativeCircuit n :=
  (QubitPrimitive.cnot c.val t c.property).circuit (QubitLayout.canonical n) .empty

private lemma nativeCnot_matrix {n : ℕ} (t : Fin n) (c : Control t) :
    (nativeCnot t c).binaryOperator =
      UnitaryOperator.ofPerm (WireAddress.cnotPerm c.val t c.property).symm := by
  exact QubitPrimitive.circuit_canonical_binaryMatrix
    (QubitPrimitive.cnot c.val t c.property) .empty OracleModel.emptyInterpretation

private lemma nativeCnot_eventCost {n : ℕ} (t : Fin n) (c : Control t) :
    (nativeCnot t c).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) := by
  exact QubitPrimitive.primitiveCircuit_eventCost
    (QubitPrimitive.cnot c.val t c.property) (QubitLayout.canonical n) .empty

/-- Ordered fan-in of the actual addressed CNOT declarations. -/
def parity {n : ℕ} (target : Fin n) : List (Control target) → NativeCircuit n
  | [] => UnitaryCircuit.identity AlgorithmGate.model .empty (nativeLayout n)
  | c :: cs => (nativeCnot target c).seq (parity target cs)

/-- Computational-label permutation of the same ordered CNOT list. -/
def parityPerm {n : ℕ} (target : Fin n) : List (Control target) →
    Equiv.Perm (Fin (2 ^ n))
  | [] => Equiv.refl _
  | c :: cs => (WireAddress.cnotPerm c.val target c.property).trans (parityPerm target cs)

lemma parity_matrix {n : ℕ} (t : Fin n) (cs : List (Control t)) :
    (parity t cs).binaryOperator = UnitaryOperator.ofPerm (parityPerm t cs).symm := by
  induction cs with
  | nil =>
    rw [parity, NativeCircuit.binaryOperator_identity]
    apply Subtype.ext
    ext x y
    simp [parityPerm, UnitaryOperator.ofPerm_entry, Matrix.one_apply]
    rfl
  | cons c cs ih =>
    rw [parity, NativeCircuit.binaryOperator_seq, ih, nativeCnot_matrix,
      UnitaryOperator.ofPerm_mul]
    rfl

lemma parity_matrix_apply {n : ℕ} (t : Fin n) (cs : List (Control t))
    (x y : Fin (2 ^ n)) :
    (parity t cs).binaryOperator x y = if x = parityPerm t cs y then 1 else 0 := by
  rw [parity_matrix, UnitaryOperator.ofPerm_entry]
  simp only [Equiv.symm_apply_eq]

/-- Sign of the computational bit on one wire. -/
def sign {n : ℕ} (x : Fin (2 ^ n)) (j : Fin n) : ℂ :=
  if bit x j then -1 else 1

lemma sign_cnot_target {n : ℕ} {c t : Fin n} (x : Fin (2 ^ n)) :
    sign (WireAddress.cnotMap c t x) t = sign x c * sign x t := by
  unfold WireAddress.cnotMap sign bit
  split <;> cases h : x.val.testBit (WireAddress.bitIndex t).val <;>
    simp_all [WireAddress.bit_flipBit_self]

lemma sign_cnot_other {n : ℕ} {c t j : Fin n} (htj : t ≠ j)
    (x : Fin (2 ^ n)) :
    sign (WireAddress.cnotMap c t x) j = sign x j := by
  unfold WireAddress.cnotMap sign bit
  split <;> simp [WireAddress.bit_flipBit_of_ne htj]

lemma sign_parity_target {n : ℕ} (t : Fin n) (cs : List (Control t))
    (x : Fin (2 ^ n)) :
    sign (parityPerm t cs x) t = (cs.map (fun c => sign x c.val)).prod * sign x t := by
  induction cs generalizing x with
  | nil => simp [parityPerm]
  | cons c cs ih =>
    change sign (parityPerm t cs (WireAddress.cnotMap c.val t x)) t = _
    rw [ih, sign_cnot_target]
    have hlist : cs.map (fun d => sign (WireAddress.cnotMap c.val t x) d.val) =
        cs.map (fun d => sign x d.val) := by
      apply List.map_congr_left
      intro d _
      exact sign_cnot_other (Ne.symm d.property) x
    rw [hlist, List.map_cons, List.prod_cons]
    ring

/-- The circuit contributes precisely one native CNOT for each control. -/
lemma parity_eventCost {n : ℕ} (t : Fin n) (cs : List (Control t)) :
    (parity t cs).eventCost =
      cs.length • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .cnot) := by
  induction cs with
  | nil => simp [parity]
  | cons c cs ih =>
    simp only [parity, UnitaryCircuit.seq_eventCost, nativeCnot_eventCost, ih,
      List.length_cons, succ_nsmul]
    rw [add_comm]

/-- Increasing support order, omitting the selected target. -/
def controls {n : ℕ} (P : PauliString n) (t : Fin n) : List (Control t) :=
  ((P.support.erase t).sort (· ≤ ·)).attach.map fun j =>
    ⟨j.val, (Finset.mem_erase.mp ((Finset.mem_sort (· ≤ ·)).mp j.property)).1⟩

lemma controls_length {n : ℕ} (P : PauliString n) (t : Fin n) (ht : t ∈ P.support) :
    (controls P t).length = P.weight - 1 := by
  simp [controls, PauliString.weight, Finset.card_erase_of_mem ht]

lemma controls_sign_prod {n : ℕ} (P : PauliString n) (t : Fin n)
    (x : Fin (2 ^ n)) :
    ((controls P t).map (fun c => sign x c.val)).prod =
      ∏ j ∈ P.support.erase t, sign x j := by
  simp only [controls, List.map_map, Function.comp_def, List.map_subtype, List.unattach_attach]
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]


lemma parity_diagonal {n : ℕ} (t : Fin n) (cs : List (Control t))
    (f : Fin (2 ^ n) → ℂ) :
    ((((parity t cs).binaryOperator)⁻¹ : UnitaryOperator (Qubits n)) :
        HilbertOperator (Qubits n)) * Matrix.diagonal f *
        ((parity t cs).binaryOperator : HilbertOperator (Qubits n)) =
      Matrix.diagonal (fun x => f (parityPerm t cs x)) := by
  let U := (parity t cs).binaryOperator
  have hswap : Matrix.diagonal f * (U : HilbertOperator (Qubits n)) =
      (U : HilbertOperator (Qubits n)) *
        Matrix.diagonal (fun x => f (parityPerm t cs x)) := by
    ext x y
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    change f x * (parity t cs).binaryOperator x y = (parity t cs).binaryOperator x y * _
    rw [parity_matrix_apply]
    split <;> simp_all
  have hunit : ((U⁻¹ : UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n)) *
      (U : HilbertOperator (Qubits n)) = 1 := by
    exact congrArg (fun V : UnitaryOperator (Qubits n) =>
      (V : HilbertOperator (Qubits n))) (inv_mul_cancel U)
  change ((U⁻¹ : UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n)) *
    Matrix.diagonal f * U = _
  rw [mul_assoc, hswap, ← mul_assoc, hunit, one_mul]

end
end QuantumAlg.Trotter.PauliRotation
