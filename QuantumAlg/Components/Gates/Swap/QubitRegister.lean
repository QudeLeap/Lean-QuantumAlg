/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Physical
import all QuantumAlg.Components.Gates.Swap.Physical
import all QuantumAlg.Components.Gates.Swap
public import QuantumAlg.Components.Gates.Swap.Coordinates
import all QuantumAlg.Components.Gates.Swap.Coordinates
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Native SWAP with the original qubit-register target

The actual three-CNOT word has the original addressed SWAP matrix on every
register state. Both exchanged inputs and all other qubits are unrestricted.
-/

namespace QuantumAlg.Gate.Swap

noncomputable section

/-- The original ordered register of physical qubits. -/
@[expose, implicit_reducible]
public def qubitLayout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

variable {width : Nat} (left right : Fin width) (distinct : left ≠ right)

private lemma selected_pair (basis : Fin width → Fin 2) :
    UnitaryCircuit.selectedInput layout (qubitLayout width) (positions left right distinct)
      (dimensions (qubitLayout width) left right distinct rfl rfl) basis =
        ![basis left, basis right] := by
  funext index
  fin_cases index <;> apply Fin.ext <;> rfl

private lemma matching_coordinates (row column : Fin width → Fin 2) :
    (fun index => row (Equiv.swap left right index)) = column ↔
      ![row right, row left] = ![column left, column right] ∧
        (qubitLayout width).restrictComplementBasis
          (Finset.univ.map (positions left right distinct)) row =
        (qubitLayout width).restrictComplementBasis
          (Finset.univ.map (positions left right distinct)) column := by
  have leftMember : left ∈ Finset.univ.map (positions left right distinct) :=
    Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have rightMember : right ∈ Finset.univ.map (positions left right distinct) :=
    Finset.mem_map.mpr ⟨1, Finset.mem_univ _, rfl⟩
  constructor
  · intro same
    constructor
    · have first := congrFun same left
      have second := congrFun same right
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at first second
      funext index
      fin_cases index
      · exact first
      · exact second
    · funext index
      have atLeft : index.val ≠ left := fun same =>
        (Finset.mem_compl.mp index.property) (same.symm ▸ leftMember)
      have atRight : index.val ≠ right := fun same =>
        (Finset.mem_compl.mp index.property) (same.symm ▸ rightMember)
      have result := congrFun same index.val
      change row index.val = column index.val
      exact (congrArg row (Equiv.swap_apply_of_ne_of_ne atLeft atRight)).symm.trans result
  · rintro ⟨selected, remaining⟩
    funext index
    by_cases atLeft : index = left
    · subst index
      rw [Equiv.swap_apply_left]
      exact congrFun selected (0 : Fin 2)
    · by_cases atRight : index = right
      · subst index
        rw [Equiv.swap_apply_right]
        exact congrFun selected (1 : Fin 2)
      · have outside : index ∈ (Finset.univ.map (positions left right distinct))ᶜ := by
          apply Finset.mem_compl.mpr
          intro member
          obtain ⟨localIndex, _, equal⟩ := Finset.mem_map.mp member
          fin_cases localIndex
          · exact atLeft equal.symm
          · exact atRight equal.symm
        have result := congrFun remaining ⟨index, outside⟩
        rw [Equiv.swap_apply_of_ne_of_ne atLeft atRight]
        exact result

/-- Execute all three CNOTs on the selected positions of the original register. -/
public def qubitCircuit (oracles : OracleModel) :
    UnitaryCircuit AlgorithmGate.model oracles (qubitLayout width) :=
  circuitAt (qubitLayout width) left right distinct rfl rfl oracles

/-- The full native word realizes the unchanged addressed SWAP, including exact phase. -/
public lemma swap_qubitCircuit_matrix (oracles : OracleModel) (environment :
  oracles.Interpretation) :
    ((qubitCircuit left right distinct oracles).matrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
        (qftSwapOperator left right distinct) := by
  classical
  rw [qubitCircuit, swap_circuitAt_matrix]
  apply Subtype.ext
  refine Matrix.ext fun (row : Fin width → Fin 2) (column : Fin width → Fin 2) => ?_
  change UnitaryCircuit.operatorAt layout (qubitLayout width) (positions left right distinct)
    (dimensions (qubitLayout width) left right distinct rfl rfl) operator row column = _
  refine (UnitaryCircuit.operatorAt_entry layout (qubitLayout width)
    (positions left right distinct) (dimensions (qubitLayout width) left right distinct rfl rfl)
    operator row column).trans ?_
  rw [selected_pair, selected_pair]
  have localEntry := UnitaryOperator.ofPerm_entry (R := layout.register)
    permutation ![row left, row right] ![column left, column right]
  have localTarget : operator ![row left, row right] ![column left, column right] =
      if ![row right, row left] = ![column left, column right] then 1 else 0 := by
    by_cases same : ![row right, row left] = ![column left, column right]
    · have original : permutation ![row left, row right] = ![column left, column right] :=
        (swap_permutation_pair (row left) (row right)).trans same
      rw [if_pos same]
      rw [if_pos original] at localEntry
      exact localEntry
    · have original : permutation ![row left, row right] ≠ ![column left, column right] :=
        fun equal => same ((swap_permutation_pair (row left) (row right)).symm.trans equal)
      rw [if_neg same]
      rw [if_neg original] at localEntry
      exact localEntry
  refine (congrArg (fun value : Complex => value *
    (if (qubitLayout width).restrictComplementBasis
      (Finset.univ.map (positions left right distinct)) row =
        (qubitLayout width).restrictComplementBasis
          (Finset.univ.map (positions left right distinct)) column then 1 else 0))
            localTarget).trans ?_
  refine Eq.trans ?_ (qftSwapOperator_coordinates_entry left right distinct row column).symm
  have matching := matching_coordinates left right distinct row column
  by_cases same : (fun index => row (Equiv.swap left right index)) = column
  · obtain ⟨selected, remaining⟩ := matching.mp same
    rw [if_pos selected, if_pos remaining, if_pos same, one_mul]
  · by_cases selected : ![row right, row left] = ![column left, column right]
    · have remaining := fun equal => same (matching.mpr ⟨selected, equal⟩)
      rw [if_pos selected, if_neg remaining, if_neg same, mul_zero]
    · rw [if_neg selected, if_neg same, zero_mul]

/-- The register implementation records the three actual native CNOT occurrences. -/
public lemma swap_qubitCircuit_events (oracles : OracleModel) :
    (qubitCircuit left right distinct oracles).eventTrace =
      [.gate .cnot, .gate .cnot, .gate .cnot] :=
  swap_circuitAt_events (qubitLayout width) left right distinct rfl rfl oracles

end

end QuantumAlg.Gate.Swap
