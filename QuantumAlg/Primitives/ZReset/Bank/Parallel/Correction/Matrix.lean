/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Unitary
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact full matrix of the selected parallel bank correction

Each matrix entry is a product of its physical one-wire identity/X entries.
The column selected by the actual measured basis is exactly the zero ket,
with no phase or discarded reference coordinate.
-/

namespace QuantumAlg.ZReset.BankParallel.Correction

noncomputable section

open scoped BigOperators
open Gate.HadamardLayer

private lemma castBasis_value {count : Nat} {source target : QuantumLayout count}
    (same : source = target) (basis : source.Basis) (index : Fin count) :
    (((same ▸ basis : target.Basis) index).val) = (basis index).val := by
  cases same
  rfl

private lemma castMatrix_entry {gates : GateModel} {oracles : OracleModel}
    {environment : oracles.Interpretation}
    {count : Nat} {source target : QuantumLayout count} (same : source = target)
    (body : UnitaryCircuit gates oracles source) (row column : target.Basis) :
    (body.castLayout same).matrix environment row column =
      body.matrix environment (same.symm ▸ row) (same.symm ▸ column) := by
  cases same
  rfl

private lemma prefixBasis (width : Nat) (basis : (layout (width + 1)).Basis) :
    (QuantumLayout.appendBasisEquiv (layout width) (lastLayout width)
      (hadamardLayer_layout_disjoint width)
      ((hadamardLayer_layout_append width).symm ▸ basis)).1 =
        (fun index : Fin width => basis index.castSucc) := by
  funext index
  apply Fin.ext
  exact castBasis_value (hadamardLayer_layout_append width).symm basis
    (Fin.castAdd 1 index)

private lemma suffixBasis (width : Nat) (basis : (layout (width + 1)).Basis) :
    (QuantumLayout.appendBasisEquiv (layout width) (lastLayout width)
      (hadamardLayer_layout_disjoint width)
      ((hadamardLayer_layout_append width).symm ▸ basis)).2 =
        (fun _ : Fin 1 => basis (Fin.last width)) := by
  funext index
  fin_cases index
  apply Fin.ext
  exact castBasis_value (hadamardLayer_layout_append width).symm basis
    (Fin.natAdd width 0)

/-- The exact one-qubit matrix entry selected by a stored correction bit. -/
def entry (selected : Bool) (row column : Fin 2) : ℂ :=
  if selected then Gate.XOp row column else if row = column then 1 else 0

private lemma last_entry (oracles : OracleModel)
    {environment : oracles.Interpretation} (width : Nat) (selected : Bool)
    (row column : (lastLayout width).Basis) :
    (last oracles width selected).matrix
      environment row column = entry selected (row 0) (column 0) := by
  cases selected with
  | false =>
      have equal : row = column ↔ row 0 = column 0 := by
        constructor
        · intro same; exact congrFun same 0
        · intro same
          funext index
          fin_cases index
          exact same
      change (if row = column then (1 : ℂ) else 0) =
        if row 0 = column 0 then 1 else 0
      exact if_congr equal rfl rfl
  | true =>
      let application := Gate.singleQubitApplication (lastLayout width) Gate.XOp 0
        (hadamardLayer_last_dimension width)
      have complement : (application.basisEquiv row).2 = (application.basisEquiv column).2 := by
        funext index
        have same : application.embedding.position (0 : Fin 1) = index.val := Subsingleton.elim _ _
        exact False.elim ((Finset.mem_compl.mp index.property)
          (same ▸ Finset.mem_map_of_mem application.embedding.position (Finset.mem_univ (0 : Fin
            1))))
      change (Gate.singleQubitAt (lastLayout width) oracles Gate.XOp 0
        (hadamardLayer_last_dimension width)).matrix
          environment row column = Gate.XOp (row 0) (column 0)
      rw [Gate.singleQubitAt_matrix_entry, if_pos complement, mul_one]
      congr 1

/-- Parallel construction retains the exact complete product matrix on the original positions. -/
lemma layer_matrix_entry (oracles : OracleModel)
    {environment : oracles.Interpretation} (width : Nat) (selected : Fin width → Bool)
    (row column : (layout width).Basis) :
    (layer oracles width selected).matrix environment row column =
      ∏ index : Fin width, entry (selected index) (row index) (column index) := by
  induction width with
  | zero =>
      have same : row = column := Subsingleton.elim _ _
      subst column
      simp [layer, UnitaryCircuit.identity_matrix]
  | succ width ih =>
      rw [layer, castMatrix_entry, UnitaryCircuit.tensor_native_matrix_entry,
        prefixBasis, prefixBasis, suffixBasis, suffixBasis]
      calc
        _ = (∏ index : Fin width,
              entry (selected index.castSucc) (row index.castSucc) (column index.castSucc)) *
            entry (selected (Fin.last width)) (row (Fin.last width)) (column (Fin.last width)) :=
          congrArg₂ (· * ·) (ih _ _ _) (last_entry oracles width _ _ _)
        _ = _ := (Fin.prod_univ_castSucc
          (fun index : Fin (width + 1) => entry (selected index) (row index) (column index))).symm

private lemma entry_measured (row column : Fin 2) :
    entry (decide (column.val = 1)) row column = if row = 0 then 1 else 0 := by
  fin_cases row <;> fin_cases column <;>
    norm_num [entry, Gate.XOp, UnitaryOperator.ofPerm_entry]

/-- The stored computational-basis outcome selects the exact phase-preserving zero column. -/
lemma layer_reset_column (oracles : OracleModel)
    {environment : oracles.Interpretation} (width : Nat)
    (row column : (layout width).Basis) :
    (layer oracles width (fun index => decide ((column index).val = 1))).matrix
      environment row column =
      if row = (layout width).zeroLabel then 1 else 0 := by
  refine (layer_matrix_entry oracles width _ row column).trans ?_
  let rowBits : Fin width → Fin 2 := row
  let columnBits : Fin width → Fin 2 := column
  change (∏ index : Fin width,
      entry (decide ((columnBits index).val = 1)) (rowBits index) (columnBits index)) =
    if rowBits = (fun _ => 0) then 1 else 0
  simp only [entry_measured]
  by_cases zero : rowBits = (fun _ => 0)
  · rw [if_pos zero, zero]
    simp
  · rw [if_neg zero]
    obtain ⟨index, different⟩ : ∃ index, rowBits index ≠ 0 := by
      by_contra allZero
      push Not at allZero
      exact zero (funext allZero)
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    exact if_neg different

/-- Arbitrary physical qubit identities preserve the same exact selected reset column. -/
lemma program_reset_column {count : Nat} (physical : QuantumLayout count)
    (qubits : ∀ index, (physical.wire index).dimension = 2) (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (row column : physical.Basis) :
    (program physical qubits oracles (fun index => decide ((column index).val = 1))).matrix
      environment row column = if row = physical.zeroLabel then 1 else 0 := by
  rw [program, UnitaryCircuit.placeAt_matrix,
    UnitaryCircuit.operatorAt_entry_of_surjective _ _ _ _ (Function.surjective_id)]
  have selected : (fun index => decide ((column index).val = 1)) =
      (fun index => decide ((UnitaryCircuit.basisAt (layout count) physical
        (Function.Embedding.refl _) (dimensions physical qubits) column index).val = 1)) := by
    rfl
  rw [selected, layer_reset_column]
  have zero : UnitaryCircuit.basisAt (layout count) physical (Function.Embedding.refl _)
      (dimensions physical qubits) row = (layout count).zeroLabel ↔
      row = physical.zeroLabel := by
    constructor
    · intro same
      funext index
      apply Fin.ext
      have value := congrArg (fun label => (label index).val) same
      simpa only [UnitaryCircuit.basisAt_val, QuantumLayout.zeroLabel,
        Function.Embedding.coe_refl, id_eq] using value
    · intro same
      subst row
      funext index
      apply Fin.ext
      rfl
  exact if_congr zero rfl rfl

end

end QuantumAlg.ZReset.BankParallel.Correction
