/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.QubitPrimitive.Operator
public import QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Native reversible gates on their declared argument values

The default model's actual X, CNOT and Toffoli operators have exact permutation
semantics on their original arguments. These proofs use the fixed big-endian
interpretation already owned by the model, including full operator phase.
-/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- The row permutation of the model's fixed two-qubit CNOT. -/
@[expose]
public def cnotPermutation : Equiv.Perm (QuantumSignature.qubits 2).Basis :=
  (((QuantumSignature.qubitsIndexEquiv 2).trans (Equiv.swap 2 3)).trans
    (QuantumSignature.qubitsIndexEquiv 2).symm)

/-- This permutation interprets the actual native token with exact phase. -/
public lemma cnot_operator_ofPerm :
    model.operator .cnot = UnitaryOperator.ofPerm cnotPermutation := by
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm
    (UnitaryOperator.ofPerm (Equiv.swap 2 3)) = _
  exact UnitaryOperator.reindex_ofPerm (QuantumSignature.qubitsIndexEquiv 2).symm _

/-- CNOT acts on the ordered control and target values, with addition in `Fin 2`. -/
public lemma cnotPermutation_pair (control target : Fin 2) :
    cnotPermutation ![control, target] = ![control, control + target] := by
  fin_cases control <;> fin_cases target
  all_goals
    funext index
    fin_cases index <;> rfl

/-- The local CNOT action reads its actual two argument coordinates. -/
public lemma cnotPermutation_apply (basis : Fin 2 → Fin 2) :
    cnotPermutation basis = ![basis 0, basis 0 + basis 1] := by
  have coordinates : basis = ![basis 0, basis 1] := by
    funext index
    fin_cases index <;> rfl
  exact (congrArg cnotPermutation coordinates).trans (cnotPermutation_pair (basis 0) (basis 1))

/-- The row permutation of the default model's exact Pauli X instance. -/
@[expose]
public def xPermutation : Equiv.Perm (QuantumSignature.qubits 1).Basis :=
  (((QuantumSignature.qubitsIndexEquiv 1).trans (Equiv.swap 0 1)).trans
    (QuantumSignature.qubitsIndexEquiv 1).symm)

/-- Pauli X is one actual single-qubit token with its complete exact-phase semantics. -/
public lemma x_operator_ofPerm :
    model.operator (.singleQubit Gate.XOp) = UnitaryOperator.ofPerm xPermutation := by
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 1).symm
    (UnitaryOperator.ofPerm (Equiv.swap 0 1)) = _
  exact UnitaryOperator.reindex_ofPerm (QuantumSignature.qubitsIndexEquiv 1).symm _

/-- The actual X token flips its one finite binary argument. -/
public lemma xPermutation_single (value : Fin 2) :
    xPermutation ![value] = ![value + 1] := by
  fin_cases value
  all_goals
    funext index
    fin_cases index
    rfl

/-- The row permutation of the model's canonical Toffoli token. -/
@[expose]
public def toffoliPermutation : Equiv.Perm (QuantumSignature.qubits 3).Basis :=
  (((QuantumSignature.qubitsIndexEquiv 3).trans
    (Equiv.swap 6 7)).trans
    (QuantumSignature.qubitsIndexEquiv 3).symm)

/-- Toffoli's permutation interpretation is proved for the model-owned native token. -/
public lemma toffoli_operator_ofPerm :
    model.operator .toffoli = UnitaryOperator.ofPerm toffoliPermutation := by
  have canonical :
      (QubitPrimitive.perm
        (.toffoli 0 1 2 (by decide) (by decide) (by decide) : QubitPrimitive 3)).symm =
        Equiv.swap 6 7 := by
    ext label
    fin_cases label <;> decide
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 3).symm
    (UnitaryOperator.ofPerm _) = _
  rw [canonical]
  exact UnitaryOperator.reindex_ofPerm (QuantumSignature.qubitsIndexEquiv 3).symm _

/-- The actual Toffoli token preserves both controls and adds their product into the target. -/
public lemma toffoliPermutation_triple (first second target : Fin 2) :
    toffoliPermutation ![first, second, target] = ![first, second, first * second + target] := by
  fin_cases first <;> fin_cases second <;> fin_cases target
  all_goals
    funext index
    fin_cases index <;> rfl

/-- The model's exact Toffoli action reads its original three argument coordinates. -/
public lemma toffoliPermutation_apply (basis : Fin 3 → Fin 2) :
    toffoliPermutation basis = ![basis 0, basis 1, basis 0 * basis 1 + basis 2] := by
  have coordinates : basis = ![basis 0, basis 1, basis 2] := by
    funext index
    fin_cases index <;> rfl
  exact (congrArg toffoliPermutation coordinates).trans
    (toffoliPermutation_triple (basis 0) (basis 1) (basis 2))

end

end QuantumAlg.AlgorithmGate
