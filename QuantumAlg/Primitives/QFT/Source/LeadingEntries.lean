/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.UnitaryCircuit
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact entries of the leading native Hadamard

The leading operation acts on wire zero and preserves every tail coordinate.
The statement concerns its actual operator on the complete register.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

open QFTPrimitive (layout)

private lemma leading_complement (n : Nat) (row column : (layout (n + 1)).Basis) :
    let application := Gate.singleQubitApplication (layout (n + 1)) Gate.HOp 0 rfl
    (application.basisEquiv row).2 = (application.basisEquiv column).2 ↔
      (fun index : Fin n => row index.succ) = (fun index : Fin n => column index.succ) := by
  let application := Gate.singleQubitApplication (layout (n + 1)) Gate.HOp 0 rfl
  have member (index : Fin (n + 1)) :
      index ∈ application.embedding.selection ↔ index = 0 := by
    change index ∈ Finset.univ.map
      (⟨fun _ : Fin 1 => (0 : Fin (n + 1)),
        fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin (n + 1)) ↔ _
    constructor
    · intro selected
      rcases Finset.mem_map.mp selected with ⟨position, _, equal⟩
      exact equal.symm
    · intro equal
      exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, equal.symm⟩
  have outside (index : Fin n) : index.succ ∈ application.embedding.selectionᶜ := by
    rw [Finset.mem_compl, member]
    exact Fin.succ_ne_zero index
  constructor
  · intro same
    funext index
    exact congrFun same ⟨index.succ, outside index⟩
  · intro same
    funext index
    have notZero : index.val ≠ 0 :=
      fun equal => (Finset.mem_compl.mp index.property) ((member index.val).mpr equal)
    change row index.val = column index.val
    rcases index with ⟨position, property⟩
    cases position using Fin.cases with
    | zero => exact False.elim (notZero rfl)
    | succ position => exact congrFun same position

/-- The actual leading Hadamard has identity action on the full tail register. -/
public lemma qftSource_leading_matrix_entry (oracles : OracleModel) (n : Nat)
    (row column : (layout (n + 1)).Basis)
    (environment : oracles.Interpretation) :
    ((leadingHadamard oracles n).matrix environment) row column =
      Gate.HOp (row 0) (column 0) *
        (if (fun index : Fin n => row index.succ) =
          (fun index : Fin n => column index.succ) then 1 else 0) := by
  classical
  change ((Gate.singleQubitAt (layout (n + 1)) oracles Gate.HOp 0 rfl).matrix environment) row
    column = _
  refine (Gate.singleQubitAt_matrix_entry (environment := environment) (layout (n + 1)) oracles
    Gate.HOp 0 rfl
    row column).trans ?_
  by_cases same : (fun index : Fin n => row index.succ) =
      (fun index : Fin n => column index.succ)
  · rw [if_pos ((leading_complement n row column).mpr same), if_pos same]
    rfl
  · rw [if_neg (fun equal => same ((leading_complement n row column).mp equal)), if_neg same]
    rfl

/-- Leading-bit coordinates expose Hadamard tensor identity, with no extra phase. -/
public lemma qftSource_leading_matrix_cons (oracles : OracleModel) (n : Nat)
    (rowHead columnHead : Fin 2) (rowTail columnTail : Fin n → Fin 2)
    (environment : oracles.Interpretation) :
    ((leadingHadamard oracles n).matrix environment) (Fin.cons rowHead rowTail) (Fin.cons
      columnHead columnTail) =
      Gate.HOp rowHead columnHead * (if rowTail = columnTail then 1 else 0) := by
  exact qftSource_leading_matrix_entry (environment := environment) oracles n _ _

end

end QuantumAlg.QuantumFourierTransform.Source
