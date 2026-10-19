/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.LCU.Basic
public import QuantumAlg.Components.Oracle.LCU
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
public import QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Primitives.LCU.Basic
import all QuantumAlg.Components.Oracle.LCU
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Oracle.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual prepare, SELECT, unprepare execution

The fixed source model grants V, inverse V and SELECT on the original family.
Every call is placed on its actual wires. The three distinct query coordinates
and complete depth belong to that same circuit [Lin22, hermfunc.tex:531-554].
-/

namespace QuantumAlg.LinearCombinationOfUnitaries
noncomputable section

variable {a n : Nat} (V : UnitaryOperator (Qubits a))
  (U : Fin (2 ^ a) → UnitaryOperator (Qubits n))

/-- A genuine ordinary or inverse preparation query on the coefficient register. -/
def preparation (a n : Nat) (inverse : Bool) :
    UnitaryCircuit AlgorithmGate.model (LCUOracle.model a n)
      (QuantumSignature.qubits a).canonicalPlacement.layout :=
  if inverse then
    .query (OracleModel.Application.onPlacement (LCUOracle.model a n)
      .unprepare (QuantumSignature.qubits a).canonicalPlacement)
  else
    .query (OracleModel.Application.onPlacement (LCUOracle.model a n)
      .prepare (QuantumSignature.qubits a).canonicalPlacement)

/-- A single SELECT query uses the complete joint register and its fixed family. -/
def selection (a n : Nat) : UnitaryCircuit AlgorithmGate.model (LCUOracle.model a n)
    (QuantumSignature.qubits (a + n)).canonicalPlacement.layout :=
  .query (OracleModel.Application.onPlacement (LCUOracle.model a n)
    .select (QuantumSignature.qubits (a + n)).canonicalPlacement)

/-- Preparation and inverse preparation have exactly their independently granted semantics. -/
lemma preparation_matrix (inverse : Bool) :
    (preparation a n inverse).binaryMatrix (LCUOracle.interpretation V U)
      = if inverse then V⁻¹ else V := by
  cases inverse <;>
    simp only [preparation, Bool.false_eq_true, ↓reduceIte, UnitaryCircuit.binaryMatrix,
      UnitaryCircuit.query_matrix, OracleModel.Application.queryApplication_onPlacement_operator]
  · change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv a)
      (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv a).symm V) = _
    exact UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv a).symm _
  · change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv a)
      (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv a).symm V⁻¹) = _
    exact UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv a).symm _

/-- The SELECT query is the registered diagonal controlled family, with exact phase. -/
lemma selection_matrix : (selection a n).binaryMatrix (LCUOracle.interpretation V U)
    = lcuSelectOp U := by
  simp only [selection, UnitaryCircuit.binaryMatrix, UnitaryCircuit.query_matrix,
    OracleModel.Application.queryApplication_onPlacement_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (a + n))
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (a + n)).symm
      (lcuSelectOp U)) = _
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv (a + n)).symm _

/-- The three actual granted calls, in execution order, on the same physical interface. -/
public def circuit (a n : Nat) : UnitaryCircuit AlgorithmGate.model (LCUOracle.model a n)
    (QuantumSignature.qubits (a + n)).canonicalPlacement.layout :=
  ((UnitaryCircuit.onBinaryPrefix n (preparation a n false)).seq (selection a n)).seq
    (UnitaryCircuit.onBinaryPrefix n (preparation a n true))

private lemma inverse_tensor_identity :
    (V⁻¹).tensor (1 : UnitaryOperator (Qubits n)) =
      (V.tensor (1 : UnitaryOperator (Qubits n))).dagger := by
  apply Subtype.ext
  change ((V.dagger).tensor (1 : UnitaryOperator (Qubits n)) :
      HilbertOperator (Qubits (a + n))) = _
  rw [UnitaryOperator.coe_tensor, UnitaryOperator.coe_dagger,
    UnitaryOperator.coe_dagger, UnitaryOperator.coe_tensor,
    HilbertOperator.conjTranspose_tensor]
  have identityMatrix : ((1 : UnitaryOperator (Qubits n)) :
      HilbertOperator (Qubits n)) = 1 := rfl
  rw [identityMatrix, Matrix.conjTranspose_one]

/-- The very circuit being counted has the original independently defined LCU operator. -/
lemma circuit_matrix : (circuit a n).binaryMatrix (LCUOracle.interpretation V U)
    = lcuWalk V U := by
  rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_binaryMatrix,
    preparation_matrix, preparation_matrix, selection_matrix]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [inverse_tensor_identity]
  rfl

/-- The exact pool distinguishes forward preparation, inverse preparation and SELECT. -/
lemma circuit_events (a n : Nat) : (circuit a n).eventCost =
    ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (LCUOracle.model a n)) (.oracle .prepare) +
    ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (LCUOracle.model a n)) (.oracle .select) +
    ResourcePool.singleton
      (model := .quantum AlgorithmGate.model (LCUOracle.model a n)) (.oracle .unprepare) := rfl

/-- Each of the three granted queries occupies one full sequential abstract step. -/
lemma circuit_depth (a n : Nat) :
    (circuit a n).evaluatedEventDepth (fun _ => 1) = 3 := rfl

end
end QuantumAlg.LinearCombinationOfUnitaries
