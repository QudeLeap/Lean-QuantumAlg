/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QuditShift.Realization
import all QuantumAlg.Components.QuditShift
import all QuantumAlg.Components.QuditShift.Realization
public import QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.Gate.Placement.Permutation
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Qubit shifts using the default native one-qubit gate

A zero shift executes the identity circuit. The only other qubit shift executes
one actual Pauli-X token at the selected physical wire. The exact operator proof
retains every spectator, including systems of other dimensions. This supplies
the explicit implementation family needed by measured reset and basis reload.
-/

namespace QuantumAlg.QuditShift

noncomputable section

private instance qubitShiftDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

private def xPermutation : Equiv.Perm (QuantumSignature.qubits 1).Basis :=
  ((QuantumSignature.qubitsIndexEquiv 1).trans (Equiv.swap 0 1)).trans
    (QuantumSignature.qubitsIndexEquiv 1).symm

private theorem x_operator_permutation :
    AlgorithmGate.model.operator (.singleQubit Gate.XOp) =
      UnitaryOperator.ofPerm xPermutation := by
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm
    (UnitaryOperator.ofPerm (Equiv.swap 0 1)) = _
  exact UnitaryOperator.reindex_ofPerm (QuantumSignature.qubitsIndexEquiv 1).symm _

private theorem xPermutation_value (basis : Fin 1 → Fin 2) :
    (xPermutation basis (0 : Fin 1)).val = ((basis 0).val + 1) % 2 := by
  have coordinates : basis = ![basis 0] := by
    funext index
    fin_cases index
    rfl
  rw [coordinates]
  generalize basis 0 = value
  fin_cases value <;> rfl

variable {count : Nat} (layout : QuantumLayout count) (wire : Fin count)
  (qubit : (layout.wire wire).dimension = 2)

private abbrev xApplication : GateModel.Application AlgorithmGate.model layout :=
  Gate.singleQubitApplication layout Gate.XOp wire qubit

private def qubitValue (basis : layout.Basis) : Fin 2 :=
  Fin.cast (congrArg PNat.val qubit) (basis wire)

private theorem x_selected (basis : layout.Basis) :
    ((xApplication layout wire qubit).basisEquiv basis).1 =
      fun _ : Fin 1 => qubitValue layout wire qubit basis := rfl

private theorem x_lift_permutation :
    (xApplication layout wire qubit).liftPermutation xPermutation =
      (labelShift layout wire 1).symm := by
  apply Equiv.ext
  intro basis
  apply ((xApplication layout wire qubit).liftPermutation_eq_iff xPermutation _ _).mpr
  constructor
  · have localAction :
        xPermutation (fun _ : Fin 1 => qubitValue layout wire qubit basis) =
          fun _ : Fin 1 =>
            qubitValue layout wire qubit ((labelShift layout wire 1).symm basis) := by
      refine funext (fun index : Fin 1 => ?_)
      have same : index = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst index
      apply Fin.ext
      rw [xPermutation_value]
      change ((basis wire).val + 1) % 2 =
        (Function.update basis wire (basis wire - 1) wire).val
      rw [Function.update_self, Fin.val_sub]
      have dimension : (layout.wire wire).dimension.val = 2 := congrArg PNat.val qubit
      have oneValue : (1 : Fin (layout.wire wire).dimension).val = 1 := by
        change 1 % (layout.wire wire).dimension.val = 1
        rw [dimension]
      rw [oneValue]
      generalize (basis wire).val = value
      rw [dimension]
      simp only [Nat.reduceSub, Nat.add_comm]
    exact ((congrArg xPermutation (x_selected layout wire qubit basis)).trans
      localAction).trans
        (x_selected layout wire qubit ((labelShift layout wire 1).symm basis)).symm
  · funext position
    have outside : position.val ≠ wire := by
      intro same
      have selected : wire ∈ (xApplication layout wire qubit).embedding.selection :=
        Finset.mem_map_of_mem (xApplication layout wire qubit).embedding.position
          (Finset.mem_univ (0 : Fin 1))
      exact (Finset.mem_compl.mp position.property) (same.symm ▸ selected)
    change basis position.val = Function.update basis wire (basis wire - 1) position.val
    rw [Function.update_of_ne outside]

private theorem x_application_operator :
    (xApplication layout wire qubit).operator = operator layout wire 1 := by
  rw [(xApplication layout wire qubit).operator_ofPerm xPermutation x_operator_permutation,
    x_lift_permutation]
  rfl

private theorem zero_shift_operator : operator layout wire 0 = 1 := by
  apply Subtype.ext
  ext row column
  rw [operator, UnitaryOperator.ofPerm_entry]
  change (if Function.update row wire (row wire - 0) = column then 1 else 0) =
    (1 : Matrix layout.Basis layout.Basis ℂ) row column
  simp [Matrix.one_apply]

/-- The actual qubit shift uses no gate at zero and one placed X otherwise. -/
public def qubitShiftCircuit (oracles : OracleModel)
    (amount : Fin (layout.wire wire).dimension) :
    UnitaryCircuit AlgorithmGate.model oracles layout :=
  if amount = 0 then UnitaryCircuit.identity AlgorithmGate.model oracles layout
  else Gate.singleQubitAt layout oracles Gate.XOp wire qubit

/-- The actual identity/X implementation equals the independent shift with exact phase. -/
public theorem qubitShiftCircuit_matrix (oracles : OracleModel)
    (amount : Fin (layout.wire wire).dimension) :
    (qubitShiftCircuit layout wire qubit oracles amount).matrix = operator layout wire amount := by
  by_cases zero : amount = 0
  · subst amount
    rw [qubitShiftCircuit, if_pos rfl, UnitaryCircuit.identity_matrix, zero_shift_operator]
  · have dimension : (layout.wire wire).dimension.val = 2 := congrArg PNat.val qubit
    have amountOne : amount = 1 := by
      apply Fin.ext
      have nonzero : amount.val ≠ 0 := fun same => zero (Fin.ext same)
      have bound : amount.val < 2 := lt_of_lt_of_eq amount.isLt dimension
      change amount.val = 1 % (layout.wire wire).dimension.val
      calc
        amount.val = 1 := by omega
        _ = 1 % (layout.wire wire).dimension.val := by rw [dimension]
    rw [qubitShiftCircuit, if_neg zero, amountOne]
    exact x_application_operator layout wire qubit

/-- Default-model qubit corrections use the same exact-realization interface as custom models. -/
public def qubitRealizations (oracles : OracleModel) :
    Realizations AlgorithmGate.model oracles layout wire := fun amount =>
  { circuit := qubitShiftCircuit layout wire qubit oracles amount
    matrix_eq := qubitShiftCircuit_matrix layout wire qubit oracles amount }

/-- The native trace charges only the X that is actually executed. -/
public theorem qubitShiftCircuit_events (oracles : OracleModel)
    (amount : Fin (layout.wire wire).dimension)
    (operations : ClassicalOpModel := .empty) :
    (qubitShiftCircuit layout wire qubit oracles amount).eventTrace operations =
      if amount = 0 then [] else [.gate .singleQubit] := by
  by_cases zero : amount = 0 <;> simp only [qubitShiftCircuit, zero, if_true, if_false]
  all_goals rfl

end

end QuantumAlg.QuditShift
