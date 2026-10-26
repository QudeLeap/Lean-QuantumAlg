/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm.Adjoint
public import QuantumAlg.Components.Gates.SingleQubit.Singleton
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
public import QuantumAlg.Core.Base.UnitaryCircuit.Adjoint.Resources
public import QuantumAlg.Core.Base.Gate.OperatorNorm.Reindex
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Components.Gates.SingleQubit.Singleton
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint.Resources
import all QuantumAlg.Core.Base.Gate.Unitary.Adjoint
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Oracle.Model

/-!
# Oracle-free native language for product formulas

The physical layout and default gate language are fixed before execution.
Binary operators below are mathematical observations of the actual word.
They do not grant arbitrary multi-qubit operators as executable instructions.
-/

namespace QuantumAlg.Trotter

noncomputable section

/-- Canonical physical qubits, in the Pauli strings' big-endian order. -/
public abbrev nativeLayout (n : Nat) : QuantumLayout n :=
  (QuantumSignature.qubits n).canonicalPlacement.layout

/-- An actual word over CNOT and arbitrary one-qubit gates, without oracle access. -/
public abbrev NativeCircuit (n : Nat) :=
  UnitaryCircuit AlgorithmGate.model OracleModel.empty (nativeLayout n)

namespace NativeCircuit

/-- Observe the complete operator in the original binary coordinates. -/
public def binaryOperator {n : Nat} (body : NativeCircuit n) : UnitaryOperator (Qubits n) :=
  body.binaryMatrix OracleModel.emptyInterpretation

@[simp] public lemma binaryOperator_identity (n : Nat) :
    binaryOperator (UnitaryCircuit.identity AlgorithmGate.model .empty (nativeLayout n)) = 1 :=
  UnitaryCircuit.unitaryCircuit_binaryMatrix_identity _ _ _ _

@[simp] public lemma binaryOperator_seq {n : Nat} (first second : NativeCircuit n) :
    binaryOperator (first.seq second) = second.binaryOperator * first.binaryOperator :=
  UnitaryCircuit.unitaryCircuit_binaryMatrix_seq _ _ _

@[simp] public lemma binaryOperator_iterate {n : Nat} (r : Nat) (body : NativeCircuit n) :
    binaryOperator (UnitaryCircuit.iterate r body) = body.binaryOperator ^ r :=
  UnitaryCircuit.unitaryCircuit_binaryMatrix_iterate _ _ _

/-- The default model realizes every inverse by an actual native gate on the same wires. -/
public def inverse {n : Nat} (body : NativeCircuit n) : NativeCircuit n :=
  body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)

@[simp] public lemma binaryOperator_inverse {n : Nat} (body : NativeCircuit n) :
    body.inverse.binaryOperator = body.binaryOperator⁻¹ := by
  unfold inverse binaryOperator UnitaryCircuit.binaryMatrix
  rw [UnitaryCircuit.dagger_matrix, UnitaryOperator.unitaryOperator_reindex_star,
    Unitary.star_eq_inv]
  rfl

/-- Native inversion preserves the original CNOT and one-qubit coordinates. -/
@[simp] public lemma inverse_eventCost {n : Nat} (body : NativeCircuit n) :
    body.inverse.eventCost = body.eventCost := by
  apply UnitaryCircuit.dagger_eventCost body (AlgorithmGate.oracleFreeAdjoints .empty)
    (AddMonoidHom.id _)
  · intro count layout application
    change ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate (AlgorithmGate.adjointApplication application).coordinate) =
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate application.coordinate)
    rw [AlgorithmGate.algorithmGate_adjointApplication_coordinate]
  · intro count layout application
    exact False.elim
      (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

/-- One actual one-qubit native instruction on its canonical wire. -/
public def single (operator : UnitaryOperator (Qubits 1)) : NativeCircuit 1 :=
  Gate.singleQubitAt (nativeLayout 1) .empty operator 0 rfl

@[simp] public lemma binaryOperator_single (operator : UnitaryOperator (Qubits 1)) :
    (single operator).binaryOperator = operator :=
  Gate.singleQubitAt_singleton_binaryMatrix .empty operator
    (environment := OracleModel.emptyInterpretation)

@[simp] public lemma single_eventCost (operator : UnitaryOperator (Qubits 1)) :
    (single operator).eventCost =
      (ResourcePool.singleton (.gate .singleQubit) :
        ResourcePool (.quantum AlgorithmGate.model .empty)) := by
  rw [single, Gate.singleQubitAt_eventCost]

/-- Recover the physical operator from its exact binary observation, in every environment. -/
public lemma matrix_eq_of_binaryOperator {n : Nat} (body : NativeCircuit n)
    (target : UnitaryOperator (Qubits n)) (same : body.binaryOperator = target)
    (environment : OracleModel.empty.Interpretation) :
    body.matrix environment =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm target := by
  have env : environment = OracleModel.emptyInterpretation := Subsingleton.elim _ _
  subst environment
  rw [← same, binaryOperator, UnitaryCircuit.binaryMatrix,
    UnitaryOperator.unitaryOperator_reindex_cancel]

/-- Transport an already proved binary operator bound to the genuine physical realization. -/
@[expose] public def approximate {n : Nat} (body : NativeCircuit n)
    (target : UnitaryOperator (Qubits n)) (ε : ℝ)
    (bound : HilbertOperator.opNorm
      ((body.binaryOperator : HilbertOperator (Qubits n)) -
        (target : HilbertOperator (Qubits n))) ≤ ε) :
    UnitaryCircuit.ApproxRealization AlgorithmGate.model .empty (nativeLayout n)
      (fun _ => UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv n).symm target) ε where
  circuit := body
  error_le environment := by
    rw [matrix_eq_of_binaryOperator body body.binaryOperator rfl environment,
      HilbertOperator.opNorm_reindex_sub]
    exact bound

end NativeCircuit
end
end QuantumAlg.Trotter
