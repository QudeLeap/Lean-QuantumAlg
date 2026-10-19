/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Actual qubit-circuit matrices in binary coordinates

This projection expresses an already constructed circuit's matrix in the
library's binary labels. It is a mathematical view, with no executable event
or permission to synthesize an arbitrary unitary as a native instruction.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {width : Nat}

/-- Express the actual physical matrix in canonical big-endian integer labels. -/
@[expose] public def binaryMatrix
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    UnitaryOperator (Qubits width) :=
  UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width) (body.matrix environment)

/-- The binary-coordinate view is the canonical basis reindexing of the
physical circuit matrix. -/
public lemma binaryMatrix_eq_reindex
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    (body.binaryMatrix environment) =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width) (body.matrix environment) :=
  rfl

/-- The binary view preserves the execution order of sequential composition. -/
public lemma unitaryCircuit_binaryMatrix_seq
    (first second : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((first.seq second).binaryMatrix environment) = (second.binaryMatrix environment) *
      (first.binaryMatrix environment) := by
  unfold binaryMatrix
  rw [seq_matrix]
  exact UnitaryOperator.unitaryOperator_reindex_mul _ (second.matrix environment) (first.matrix
    environment)

/-- The empty physical circuit remains the identity in binary labels. -/
public lemma unitaryCircuit_binaryMatrix_identity (gates : GateModel) (oracles : OracleModel)
    (width : Nat) (environment : oracles.Interpretation) :
    binaryMatrix
      (identity gates oracles (QuantumSignature.qubits width).canonicalPlacement.layout)
        environment =
      (1 : UnitaryOperator (Qubits width)) := by
  unfold binaryMatrix
  rw [identity_matrix, UnitaryOperator.unitaryOperator_reindex_one]

/-- A descriptive macro boundary leaves the complete binary-coordinate operator unchanged. -/
public lemma unitaryCircuit_binaryMatrix_macroCall (name : String)
    (body : UnitaryCircuit gates oracles
      (QuantumSignature.qubits width).canonicalPlacement.layout) (environment :
        oracles.Interpretation) :
    ((macroCall name body).binaryMatrix environment) = (body.binaryMatrix environment) := by
  unfold binaryMatrix
  rw [macroCall_matrix]

end

end QuantumAlg.UnitaryCircuit
