/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.SingleQubit.Entries
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import Mathlib.Data.Fin.Tuple.Basic

/-!
# An actual final-wire operation preserves the whole prefix

The one-qubit native operation acts on the last canonical wire. Every earlier
wire is retained in the exact matrix entry, without an initialization assumption.
-/

namespace QuantumAlg.Gate

noncomputable section

private abbrev layout (width : Nat) :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

private theorem final_complement (width : Nat) (operator : UnitaryOperator (Qubits 1))
    (row column : (layout (width + 1)).Basis) :
    let application := singleQubitApplication (layout (width + 1)) operator (Fin.last width) rfl
    (application.basisEquiv row).2 = (application.basisEquiv column).2 ↔
      (fun index : Fin width => row index.castSucc) =
        (fun index : Fin width => column index.castSucc) := by
  let application := singleQubitApplication (layout (width + 1)) operator (Fin.last width) rfl
  have member (index : Fin (width + 1)) :
      index ∈ application.embedding.selection ↔ index = Fin.last width := by
    change index ∈ Finset.univ.map
      (⟨fun _ : Fin 1 => Fin.last width,
        fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin (width + 1)) ↔ _
    constructor
    · intro selected
      rcases Finset.mem_map.mp selected with ⟨position, _, equal⟩
      exact equal.symm
    · intro equal
      exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, equal.symm⟩
  have outside (index : Fin width) : index.castSucc ∈ application.embedding.selectionᶜ := by
    rw [Finset.mem_compl, member]
    intro same
    have values := congrArg Fin.val same
    change index.val = width at values
    omega
  constructor
  · intro same
    funext index
    exact congrFun same ⟨index.castSucc, outside index⟩
  · intro same
    funext index
    have notLast : index.val ≠ Fin.last width :=
      fun equal => (Finset.mem_compl.mp index.property) ((member index.val).mpr equal)
    change row index.val = column index.val
    rcases index with ⟨position, property⟩
    cases position using Fin.lastCases with
    | last => exact False.elim (notLast rfl)
    | cast position => exact congrFun same position

/-- The final native operation has identity action on the complete original prefix. -/
public theorem singleQubitAt_last_matrix_entry (oracles : OracleModel) (width : Nat)
    (operator : UnitaryOperator (Qubits 1))
    (row column : (QuantumSignature.qubits (width + 1)).Basis) :
    (singleQubitAt (QuantumSignature.qubits (width + 1)).canonicalPlacement.layout
      oracles operator (Fin.last width) rfl).matrix row column =
      operator (row (Fin.last width)) (column (Fin.last width)) *
        (if (fun index : Fin width => row index.castSucc) =
          (fun index : Fin width => column index.castSucc) then 1 else 0) := by
  classical
  refine (singleQubitAt_matrix_entry (layout (width + 1)) oracles operator
    (Fin.last width) rfl row column).trans ?_
  by_cases same : (fun index : Fin width => row index.castSucc) =
      (fun index : Fin width => column index.castSucc)
  · rw [if_pos ((final_complement width operator row column).mpr same), if_pos same]
    rfl
  · rw [if_neg (fun equal => same ((final_complement width operator row column).mp equal)),
      if_neg same]
    rfl

end

end QuantumAlg.Gate
