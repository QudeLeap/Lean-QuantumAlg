/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Native one-qubit support at arbitrary physical positions

The matrix uses the actual selected wire value. Every other physical wire
must agree, regardless of its local dimension or initial correlations.
-/

namespace QuantumAlg.Gate

noncomputable section

/-- The native one-qubit complement is precisely every other actual wire. -/
public lemma singleQubitAt_complement_eq_iff {count : Nat}
    (ambient : QuantumLayout count) (operator : UnitaryOperator (Qubits 1))
    (target : Fin count) (qubit : (ambient.wire target).dimension = 2)
    (row column : ambient.Basis) :
    ((singleQubitApplication ambient operator target qubit).basisEquiv row).2 =
        ((singleQubitApplication ambient operator target qubit).basisEquiv column).2 ↔
      ∀ index : Fin count, index ≠ target → row index = column index := by
  let application := singleQubitApplication ambient operator target qubit
  have member (index : Fin count) :
      index ∈ application.embedding.selection ↔ index = target := by
    change index ∈ Finset.univ.map
      (⟨fun _ : Fin 1 => target,
        fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin count) ↔ _
    constructor
    · intro selected
      rcases Finset.mem_map.mp selected with ⟨position, _, equal⟩
      exact equal.symm
    · intro equal
      exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, equal.symm⟩
  constructor
  · intro equal index different
    have outside : index ∈ application.embedding.selectionᶜ := by
      rw [Finset.mem_compl, member]
      exact different
    exact congrFun equal ⟨index, outside⟩
  · intro equal
    funext index
    change row index.val = column index.val
    exact equal index.val (fun same =>
      (Finset.mem_compl.mp index.property) ((member index.val).mpr same))

/-- A native operation has identity action on all other actual physical systems. -/
public lemma singleQubitAt_matrix_entry_outside {count : Nat}
    (ambient : QuantumLayout count) (oracles : OracleModel)
    (operator : UnitaryOperator (Qubits 1)) (target : Fin count)
    (qubit : (ambient.wire target).dimension = 2) (row column : ambient.Basis)
      (environment : oracles.Interpretation) :
    ((singleQubitAt ambient oracles operator target qubit).matrix environment) row column =
      operator
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (row target))
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (column target)) *
          (if ∀ index : Fin count, index ≠ target → row index = column index
            then 1 else 0) := by
  classical
  rw [singleQubitAt_matrix_entry]
  simp only [singleQubitAt_complement_eq_iff]

end

end QuantumAlg.Gate
