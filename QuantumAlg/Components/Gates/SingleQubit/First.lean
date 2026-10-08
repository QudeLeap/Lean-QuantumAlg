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
# An actual leading-wire operation preserves the whole suffix

The one-qubit native operation acts on the first canonical wire. Every trailing
wire is retained in the exact matrix entry, without an initialization assumption.
-/

namespace QuantumAlg.Gate

noncomputable section

private abbrev layout (width : Nat) :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

private theorem first_complement (width : Nat) (operator : UnitaryOperator (Qubits 1))
    (row column : (layout (1 + width)).Basis) :
    let application :=
      singleQubitApplication (layout (1 + width)) operator (0 : Fin (1 + width)) rfl
    (application.basisEquiv row).2 = (application.basisEquiv column).2 ↔
      (fun index : Fin width => row (Fin.natAdd 1 index)) =
        (fun index : Fin width => column (Fin.natAdd 1 index)) := by
  let application := singleQubitApplication (layout (1 + width)) operator (0 : Fin (1 + width)) rfl
  have member (index : Fin (1 + width)) :
      index ∈ application.embedding.selection ↔ index = (0 : Fin (1 + width)) := by
    change index ∈ Finset.univ.map
      (⟨fun _ : Fin 1 => (0 : Fin (1 + width)),
        fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin (1 + width)) ↔ _
    constructor
    · intro selected
      rcases Finset.mem_map.mp selected with ⟨position, _, equal⟩
      exact equal.symm
    · intro equal
      exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, equal.symm⟩
  have outside (index : Fin width) : (Fin.natAdd 1 index) ∈ application.embedding.selectionᶜ := by
    rw [Finset.mem_compl, member]
    intro same
    have values := congrArg Fin.val same
    change 1 + index.val = 0 at values
    omega
  constructor
  · intro same
    funext index
    exact congrFun same ⟨(Fin.natAdd 1 index), outside index⟩
  · intro same
    funext index
    have notFirst : index.val ≠ (0 : Fin (1 + width)) :=
      fun equal => (Finset.mem_compl.mp index.property) ((member index.val).mpr equal)
    change row index.val = column index.val
    rcases index with ⟨position, property⟩
    induction position using Fin.addCases with
    | left first =>
      fin_cases first
      exact False.elim (notFirst rfl)
    | right tail => exact congrFun same tail

/-- The leading native operation has identity action on the complete original suffix. -/
public theorem singleQubitAt_first_matrix_entry (oracles : OracleModel) (width : Nat)
    (operator : UnitaryOperator (Qubits 1))
    (row column : (QuantumSignature.qubits (1 + width)).Basis) :
    (singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
      oracles operator (0 : Fin (1 + width)) rfl).matrix row column =
      operator (row (0 : Fin (1 + width))) (column (0 : Fin (1 + width))) *
        (if (fun index : Fin width => row (Fin.natAdd 1 index)) =
          (fun index : Fin width => column (Fin.natAdd 1 index)) then 1 else 0) := by
  classical
  refine (singleQubitAt_matrix_entry (layout (1 + width)) oracles operator
    (0 : Fin (1 + width)) rfl row column).trans ?_
  by_cases same : (fun index : Fin width => row (Fin.natAdd 1 index)) =
      (fun index : Fin width => column (Fin.natAdd 1 index))
  · rw [if_pos ((first_complement width operator row column).mpr same), if_pos same]
    rfl
  · rw [if_neg (fun equal => same ((first_complement width operator row column).mp equal)),
      if_neg same]
    rfl

end

end QuantumAlg.Gate
