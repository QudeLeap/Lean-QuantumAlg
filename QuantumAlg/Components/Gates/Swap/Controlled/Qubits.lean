/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.Swap.Controlled.Physical
public import QuantumAlg.Core.Base.UnitaryCircuit.Placement.Permutation
import all QuantumAlg.Components.Gates.Swap.Controlled.Physical
import all QuantumAlg.Components.Gates.Swap.Controlled
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Permutation
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Complete basis action of a native controlled swap inside a qubit register

The original control selects an actual exchange of the two target coordinates.
Every other coordinate remains unchanged, with no input-state restriction.
-/

namespace QuantumAlg.Gate.ControlledSwap

noncomputable section

variable {width : Nat} (control left right : Fin width)
variable (controlLeft : control ≠ left) (controlRight : control ≠ right) (leftRight : left ≠ right)

private abbrev qubits : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- Independent coordinate action of a controlled exchange on the original qubits. -/
public def qubitAction (basis : Fin width → Fin 2) : Fin width → Fin 2 :=
  if basis control = 0 then basis else fun index => basis (Equiv.swap left right index)

include controlLeft controlRight in
private lemma action_control (basis : Fin width → Fin 2) :
    qubitAction control left right basis control = basis control := by
  simp only [qubitAction]
  split
  · rfl
  · exact congrArg basis (Equiv.swap_apply_of_ne_of_ne controlLeft controlRight)

include controlLeft controlRight in
private lemma action_involution (basis : Fin width → Fin 2) :
    qubitAction control left right (qubitAction control left right basis) = basis := by
  unfold qubitAction
  have fixed := action_control control left right controlLeft controlRight basis
  unfold qubitAction at fixed
  rw [fixed]
  split
  · rfl
  · funext index
    exact congrArg basis (Equiv.swap_apply_self left right index)

/-- The complete independent action is an involutive basis permutation. -/
public def qubitPermutation :
    Equiv.Perm (QuantumSignature.qubits width).canonicalPlacement.layout.Basis where
  toFun := qubitAction control left right
  invFun := qubitAction control left right
  left_inv := action_involution control left right controlLeft controlRight
  right_inv := action_involution control left right controlLeft controlRight

private lemma placed_permutation :
    UnitaryCircuit.permutationAt layout qubits
      (positions control left right controlLeft controlRight leftRight)
      (dimensions qubits control left right controlLeft controlRight leftRight rfl rfl rfl)
      permutation = qubitPermutation control left right controlLeft controlRight := by
  apply Equiv.ext
  intro basis
  change Fin width → Fin 2 at basis
  apply (UnitaryCircuit.permutationAt_eq_iff _ _ _ _ _ _ _).mpr
  have selected (values : Fin width → Fin 2) :
      UnitaryCircuit.selectedInput layout qubits
        (positions control left right controlLeft controlRight leftRight)
        (dimensions qubits control left right controlLeft controlRight leftRight rfl rfl rfl)
        values = ![values control, values left, values right] := by
    funext index
    fin_cases index <;> apply Fin.ext <;> rfl
  constructor
  · refine (congrArg permutation (selected basis)).trans ?_
    refine (controlledSwap_permutation_triple (basis control) (basis left) (basis right)).trans ?_
    refine Eq.trans ?_ (selected (qubitAction control left right basis)).symm
    rw [action_control control left right controlLeft controlRight]
    by_cases zero : basis control = 0
    · simp only [qubitAction, zero, if_pos]
      rfl
    · simp only [qubitAction, zero, if_false, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rfl
  · funext index
    have outside := Finset.mem_compl.mp index.property
    have notLeft : index.val ≠ left := by
      intro same
      apply outside
      rw [same]
      exact Finset.mem_map.mpr ⟨1, Finset.mem_univ _, rfl⟩
    have notRight : index.val ≠ right := by
      intro same
      apply outside
      rw [same]
      exact Finset.mem_map.mpr ⟨2, Finset.mem_univ _, rfl⟩
    change basis index.val = qubitAction control left right basis index.val
    by_cases zero : basis control = 0
    · simp only [qubitAction, zero, if_pos]
    · simp only [qubitAction, zero]
      exact (congrArg basis (Equiv.swap_apply_of_ne_of_ne notLeft notRight)).symm

/-- Exact native semantics on every computational coordinate, including all spectators. -/
public lemma controlledSwap_qubits_matrix (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    ((circuitAt (QuantumSignature.qubits width).canonicalPlacement.layout
      control left right controlLeft controlRight leftRight
      rfl rfl rfl oracles).matrix environment) =
      UnitaryOperator.ofPerm (qubitPermutation control left right controlLeft controlRight) := by
  rw [controlledSwap_circuitAt_matrix, placedOperator, operator,
    UnitaryCircuit.operatorAt_ofPerm]
  exact congrArg UnitaryOperator.ofPerm
    (placed_permutation control left right controlLeft controlRight leftRight)

end

end QuantumAlg.Gate.ControlledSwap
