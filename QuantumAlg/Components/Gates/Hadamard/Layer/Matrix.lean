/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Components.Gates.Hadamard.Layer
import all QuantumAlg.Components.Gates.Hadamard.Layer.Layout
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Gate.Unitary
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact physical matrix of the parallel Hadamard layer

Each matrix entry is the product of the actual one-qubit Hadamard entries
at the original wire positions. This retains the full tensor action and phase.
-/

namespace QuantumAlg.Gate.HadamardLayer

noncomputable section

open scoped BigOperators

private lemma castBasis_value {count : Nat} {source target : QuantumLayout count}
    (same : source = target) (basis : source.Basis) (index : Fin count) :
    (((same ▸ basis : target.Basis) index).val) = (basis index).val := by
  cases same
  rfl

private lemma castMatrix_entry {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {source target : QuantumLayout count} (same : source = target)
    (body : UnitaryCircuit gates oracles source) (row column : target.Basis) (environment :
      oracles.Interpretation) :
    ((body.castLayout same).matrix environment) row column =
      (body.matrix environment) (same.symm ▸ row) (same.symm ▸ column) := by
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

private lemma lastGate_entry (oracles : OracleModel) (width : Nat)
    (row column : (lastLayout width).Basis) (environment : oracles.Interpretation) :
    ((Gate.singleQubitAt (lastLayout width) oracles Gate.HOp 0
          (hadamardLayer_last_dimension width)).matrix environment) row column =
      Gate.HOp (row 0) (column 0) := by
  let application := Gate.singleQubitApplication (lastLayout width) Gate.HOp 0
          (hadamardLayer_last_dimension width)
  have complement : (application.basisEquiv row).2 = (application.basisEquiv column).2 := by
    funext index
    have same : application.embedding.position (0 : Fin 1) = index.val := Subsingleton.elim _ _
    exact False.elim ((Finset.mem_compl.mp index.property)
      (same ▸ Finset.mem_map_of_mem application.embedding.position (Finset.mem_univ (0 : Fin 1))))
  rw [Gate.singleQubitAt_matrix_entry, if_pos complement, mul_one]
  congr 1

/-- Exact full tensor entries, including all phases, of the generated parallel native word. -/
public lemma hadamardLayer_circuit_matrix_entry (oracles : OracleModel) (width : Nat)
    (row column : (layout width).Basis) (environment : oracles.Interpretation) :
    ((circuit oracles width).matrix environment) row column =
      ∏ index : Fin width, Gate.HOp (row index) (column index) := by
  induction width with
  | zero =>
      have same : row = column := Subsingleton.elim _ _
      subst column
      simp [circuit, UnitaryCircuit.identity_matrix]
  | succ width ih =>
      rw [circuit, castMatrix_entry, UnitaryCircuit.tensor_native_matrix_entry,
        prefixBasis, prefixBasis, suffixBasis, suffixBasis]
      calc
        _ = (∏ index : Fin width, Gate.HOp (row index.castSucc) (column index.castSucc)) *
            Gate.HOp (row (Fin.last width)) (column (Fin.last width)) :=
          congrArg₂ (· * ·) (ih _ _) (lastGate_entry oracles width _ _ environment)
        _ = _ := (Fin.prod_univ_castSucc
          (fun index : Fin (width + 1) => (Gate.HOp (row index) (column index) : ℂ))).symm

end

end QuantumAlg.Gate.HadamardLayer
