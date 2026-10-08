/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.QubitPrimitive.Adjoint
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Placement
import all QuantumAlg.Core.Base.Gate.Model
import all QuantumAlg.Core.Base.Gate.Unitary.Adjoint
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Adjoint
import all QuantumAlg.Core.Base.Oracle.Model

/-!
# Native adjoints in the default algorithm language

Toffoli and CNOT retain their original tokens. An arbitrary one-qubit unitary
is replaced by its actual adjoint parameter on the same physical system.
Every replacement is one native instruction with the same coordinate.
Oracle inverses require a separate implementation supplied by the caller.
-/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- Replace a default native gate by its inverse on exactly the original physical wires. -/
public def adjointApplication {count : Nat} {layout : QuantumLayout count}
    (application : GateModel.Application model layout) : GateModel.Application model layout := by
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  cases token with
  | toffoli => exact ⟨⟨.toffoli, placement⟩, embedding⟩
  | cnot => exact ⟨⟨.cnot, placement⟩, embedding⟩
  | singleQubit operator => exact ⟨⟨.singleQubit (star operator), placement⟩, embedding⟩

private theorem cnot_operator_star : star Gate.CNOTOp = Gate.CNOTOp := by
  apply Subtype.ext
  ext row column
  change star (Gate.CNOTOp column row) = Gate.CNOTOp row column
  fin_cases row <;> fin_cases column <;>
    simp [Gate.CNOTOp, UnitaryOperator.ofPerm_entry, Equiv.swap_apply_def]

/-- The replacement has the exact adjoint operator, including all untouched spectator systems. -/
public theorem algorithmGate_adjointApplication_operator {count : Nat}
    {layout : QuantumLayout count} (application : GateModel.Application model layout) :
    (adjointApplication application).operator = star application.operator := by
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  cases token with
  | toffoli =>
      change embedding.liftOperator (UnitaryOperator.reindex placement.indexEquiv.symm
        (model.operator .toffoli)) = star (embedding.liftOperator
          (UnitaryOperator.reindex placement.indexEquiv.symm (model.operator .toffoli)))
      rw [← QuantumLayout.Embedding.embedding_liftOperator_star,
        ← UnitaryOperator.unitaryOperator_reindex_star]
      congr 2
      change UnitaryOperator.reindex _ (QubitPrimitive.operator _) =
        star (UnitaryOperator.reindex _ (QubitPrimitive.operator _))
      rw [← UnitaryOperator.unitaryOperator_reindex_star,
        QubitPrimitive.qubitPrimitive_operator_star]
  | cnot =>
      change embedding.liftOperator (UnitaryOperator.reindex placement.indexEquiv.symm
        (model.operator .cnot)) = star (embedding.liftOperator
          (UnitaryOperator.reindex placement.indexEquiv.symm (model.operator .cnot)))
      rw [← QuantumLayout.Embedding.embedding_liftOperator_star,
        ← UnitaryOperator.unitaryOperator_reindex_star]
      congr 2
      change UnitaryOperator.reindex _ Gate.CNOTOp = star (UnitaryOperator.reindex _ Gate.CNOTOp)
      rw [← UnitaryOperator.unitaryOperator_reindex_star, cnot_operator_star]
  | singleQubit operator =>
      change embedding.liftOperator (UnitaryOperator.reindex placement.indexEquiv.symm
        (UnitaryOperator.reindex _ (star operator))) =
          star (embedding.liftOperator (UnitaryOperator.reindex placement.indexEquiv.symm
            (UnitaryOperator.reindex _ operator)))
      rw [UnitaryOperator.unitaryOperator_reindex_star,
        UnitaryOperator.unitaryOperator_reindex_star,
        QuantumLayout.Embedding.embedding_liftOperator_star]

/-- Default-model inversion preserves the native coordinate of each actual gate. -/
public theorem algorithmGate_adjointApplication_coordinate {count : Nat}
    {layout : QuantumLayout count} (application : GateModel.Application model layout) :
    (adjointApplication application).coordinate = application.coordinate := by
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  cases token <;> rfl

/-- One actual native instruction realizes the adjoint of a default-model gate application. -/
public def nativeAdjoint (oracles : OracleModel) {count : Nat} {layout : QuantumLayout count}
    (application : GateModel.Application model layout) :
    UnitaryCircuit.ExactRealization model oracles layout (star application.operator) where
  circuit := UnitaryCircuit.native (adjointApplication application)
  matrix_eq := (UnitaryCircuit.native_matrix _).trans
    (algorithmGate_adjointApplication_operator application)

/-- Use native default-model inverses and only the explicitly supplied inverse query words. -/
public def adjointRealizations (sourceOracles targetOracles : OracleModel)
    (inverseQuery : {count : Nat} → {layout : QuantumLayout count} →
      (application : OracleModel.Application sourceOracles layout) →
        UnitaryCircuit.ExactRealization model targetOracles layout (star application.operator)) :
    UnitaryCircuit.AdjointRealizations model sourceOracles model targetOracles where
  native := nativeAdjoint targetOracles
  query := inverseQuery

/-- An oracle-free source requires no inverse access, even in a target with declared queries. -/
public def oracleFreeAdjoints (targetOracles : OracleModel) :
    UnitaryCircuit.AdjointRealizations model .empty model targetOracles :=
  adjointRealizations .empty targetOracles fun application =>
    False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

end

end QuantumAlg.AlgorithmGate
