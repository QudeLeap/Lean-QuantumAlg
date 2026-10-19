/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
public import QuantumAlg.Components.Control
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Components.Control
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Granted controlled-unitary access for quantum phase processing

The QPP signal has exactly two query forms: control-on-one `U` and
control-on-zero `U†`. Both act on the ancilla followed by the original target
systems, and both count as one controlled-unitary query. The declaration owns
their common query coordinate. The execution environment supplies the operators.
-/

namespace QuantumAlg.QSP.MultiQubit.QPPOracle

noncomputable section

/-- The two controlled access forms used by the alternating QPP word. -/
public inductive Query where
  | forward
  | inverseZero
  deriving DecidableEq

/-- One occurrence of either access form is one controlled query. -/
public inductive Coordinate where
  | controlled
  deriving DecidableEq

/-- The public source width fixes the two controlled signal forms. -/
@[expose, implicit_reducible]
public def model (n : Nat) : OracleModel where
  Query := Query
  Coordinate := Coordinate
  coordinateDecidableEq := inferInstance
  signature _ := QuantumSignature.qubits (1 + n)
  coordinate _ := .controlled

/-- The hidden source operator interprets the fixed two-query interface. -/
public def interpretation {n : Nat} (U : UnitaryOperator (Qubits n)) :
    (model n).Interpretation where
  operator
    | .forward =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n)).symm
          (UnitaryOperator.controlledQubits U)
    | .inverseZero =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n)).symm
          (UnitaryOperator.controlledQubitsOnZero U⁻¹)

/-- Every permitted access form is a controlled call on the complete ancilla-target word. -/
public lemma query_signature (n : Nat)
    (query : Query) :
    (model n).signature query = QuantumSignature.qubits (1 + n) := by
  cases query <;> rfl

/-- The declaration grants exactly the two controlled forms used by QPP. -/
public lemma query_cases (query : Query) :
    query = .forward ∨ query = .inverseZero := by
  cases query with
  | forward => exact Or.inl rfl
  | inverseZero => exact Or.inr rfl

/-- Both declared forms share the controlled-query accounting coordinate. -/
@[expose]
public def event (n : Nat) :
    Resource.Event (.quantum AlgorithmGate.model (model n)) :=
  .oracle .controlled

/-- Execute one granted QPP signal query on the canonical ancilla and target layout. -/
@[expose]
public def circuit (n : Nat) (query : Query) :
    UnitaryCircuit AlgorithmGate.model (model n)
      (QuantumSignature.qubits (1 + n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.onPlacement (model n) query
    (QuantumSignature.qubits (1 + n)).canonicalPlacement)

/-- The forward query has the declared controlled-`U` matrix in binary coordinates. -/
public lemma circuit_forward_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n)) :
    ((circuit n .forward).binaryMatrix
      (interpretation U)) = UnitaryOperator.controlledQubits U := by
  rw [circuit, UnitaryCircuit.binaryMatrix, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n))
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n)).symm
      (UnitaryOperator.controlledQubits U)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (1 + n)).symm _

/-- The inverse query has the declared zero-controlled-`U†` matrix. -/
public lemma circuit_inverseZero_binaryMatrix {n : Nat} (U : UnitaryOperator (Qubits n)) :
    ((circuit n .inverseZero).binaryMatrix (interpretation U)) =
      UnitaryOperator.controlledQubitsOnZero U⁻¹ := by
  rw [circuit, UnitaryCircuit.binaryMatrix, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n))
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + n)).symm
      (UnitaryOperator.controlledQubitsOnZero U⁻¹)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (1 + n)).symm _

/-- Every executed signal query is counted in the declared controlled coordinate. -/
public lemma circuit_eventCost (n : Nat)
    (query : Query) :
    (circuit n query).eventCost = ResourcePool.singleton (event n) := by
  cases query <;> rfl

end

end QuantumAlg.QSP.MultiQubit.QPPOracle
