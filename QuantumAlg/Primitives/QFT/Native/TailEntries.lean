/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Native
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact matrix entries of the recursive native QFT tail

The tail uses the original successor positions. Its complete operator acts
on those coordinates and preserves the leading qubit, including coherences.
-/

namespace QuantumAlg.QuantumFourierTransform.Native

noncomputable section

open QFTPrimitive (layout)

private theorem tail_complement (n : Nat) (row column : (layout (n + 1)).Basis) :
    (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) row =
      (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) column ↔ row 0 = column 0 := by
  have zeroOutside : (0 : Fin (n + 1)) ∈
      (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩)ᶜ := by
    simp
  constructor
  · intro same
    exact congrFun same ⟨0, zeroOutside⟩
  · intro same
    funext index
    have isZero : index.val = 0 := by
      have outside := Finset.mem_compl.mp index.property
      rcases index with ⟨position, member⟩
      cases position using Fin.cases with
      | zero => rfl
      | succ position =>
          exact False.elim (outside (Finset.mem_map.mpr
            ⟨position, Finset.mem_univ _, rfl⟩))
    change row index.val = column index.val
    rw [isZero]
    exact same

/-- Placing the recursive word leaves precisely the leading coordinate untouched. -/
public theorem qftNative_tail_matrix_entry (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit AlgorithmGate.model oracles (layout n))
    (row column : (layout (n + 1)).Basis) :
    (tailLayer oracles n body).matrix row column =
      body.matrix (fun index => row index.succ) (fun index => column index.succ) *
        (if row 0 = column 0 then 1 else 0) := by
  classical
  have placed := UnitaryCircuit.placeAt_matrix (layout n) (layout (n + 1))
    ⟨Fin.succ, Fin.succ_injective n⟩ (fun _ => rfl) body
  refine (congrArg (fun operator : UnitaryOperator (layout (n + 1)).register =>
    operator row column) placed).trans ?_
  refine (UnitaryCircuit.operatorAt_entry (layout n) (layout (n + 1))
    ⟨Fin.succ, Fin.succ_injective n⟩ (fun _ => rfl) body.matrix row column).trans ?_
  change body.matrix (fun index => row index.succ) (fun index => column index.succ) *
    (if (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) row =
      (layout (n + 1)).restrictComplementBasis
        (Finset.univ.map ⟨Fin.succ, Fin.succ_injective n⟩) column then 1 else 0) = _
  by_cases same : row 0 = column 0
  · rw [if_pos ((tail_complement n row column).mpr same), if_pos same]
  · rw [if_neg (fun equal => same ((tail_complement n row column).mp equal)), if_neg same]

/-- In leading-bit and tail coordinates, the placed word is identity tensor its original matrix. -/
public theorem qftNative_tail_matrix_cons (oracles : OracleModel) (n : Nat)
    (body : UnitaryCircuit AlgorithmGate.model oracles (layout n))
    (rowHead columnHead : Fin 2) (rowTail columnTail : Fin n → Fin 2) :
    (tailLayer oracles n body).matrix (Fin.cons rowHead rowTail) (Fin.cons columnHead columnTail) =
      body.matrix rowTail columnTail * (if rowHead = columnHead then 1 else 0) := by
  exact qftNative_tail_matrix_entry oracles n body _ _

end

end QuantumAlg.QuantumFourierTransform.Native
