/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Components.BinaryLabelEncoding
public import QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Exact scalar transport on actual encoded prefix programs

The width is symbolic. A complete retained suffix is tensored with the
actual source program, retaining its coefficient and all coherent phases.
No additional executed operator or physical system is introduced.
-/

namespace QuantumAlg.UnitaryCircuit.Realizes

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {environment : oracles.Interpretation}

public lemma binaryMatrix_applyVec_encoded_ket_smul {width : Nat}
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical width).toQuantum)
    (input output : Fin (2 ^ width)) (coefficient : ℂ)
    (actual : body.applyVec environment
      (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm input)).vec =
        coefficient •
          (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm output)).vec) :
    (body.binaryMatrix environment).applyVec (NormalizedVector.ket input).vec =
      coefficient • (NormalizedVector.ket output).vec := by
  ext binaryIndex
  have entry := congrArg
    (fun vector : HilbertVector (QubitLayout.canonical width).toQuantum.register =>
      vector ((QubitLayout.canonical width).basisEquiv.symm binaryIndex)) actual
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at entry
  change (body.binaryMatrix environment).applyVec (NormalizedVector.ket input).vec binaryIndex = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  convert entry using 1 <;>
    simp [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex,
      Matrix.reindex_apply, Matrix.submatrix_apply, NormalizedVector.ket_apply,
      QubitLayout.basisEquiv, PiLp.smul_apply]
  all_goals rfl

public lemma applyVec_encoded_ket_smul_of_binaryMatrix {width : Nat}
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical width).toQuantum)
    (input output : Fin (2 ^ width)) (coefficient : ℂ)
    (actual : (body.binaryMatrix environment).applyVec (NormalizedVector.ket input).vec =
      coefficient • (NormalizedVector.ket output).vec) :
    body.applyVec environment
      (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm input)).vec =
        coefficient •
          (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm output)).vec := by
  ext physicalIndex
  have entry := congrArg (fun vector : HilbertVector (Qubits width) =>
    vector ((QubitLayout.canonical width).basisEquiv physicalIndex)) actual
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at entry
  change body.applyVec environment
    (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm input)).vec
      physicalIndex = _
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  convert entry using 1 <;>
    simp [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex,
      Matrix.reindex_apply, Matrix.submatrix_apply, NormalizedVector.ket_apply,
      QubitLayout.basisEquiv, Equiv.eq_symm_apply, PiLp.smul_apply]
  all_goals rfl

/-- The real prefix placement retains both the full suffix and the exact source coefficient. -/
public lemma onBinaryPrefix_applyVec_encoded_ket_of_smul {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (body : UnitaryCircuit gates oracles (QubitLayout.canonical left.width).toQuantum)
    (input output : Left) (extra : Right) (coefficient : ℂ)
    (actual : body.applyVec environment
      (NormalizedVector.ket ((QubitLayout.canonical left.width).basisEquiv.symm
        (left.encode input))).vec =
      coefficient • (NormalizedVector.ket ((QubitLayout.canonical left.width).basisEquiv.symm
        (left.encode output))).vec) :
    (UnitaryCircuit.onBinaryPrefix right.width body).applyVec environment
      (NormalizedVector.ket ((QubitLayout.canonical (left.width + right.width)).basisEquiv.symm
        (prodEquiv (left.encode input, right.encode extra)))).vec =
      coefficient • (NormalizedVector.ket
        ((QubitLayout.canonical (left.width + right.width)).basisEquiv.symm
          (prodEquiv (left.encode output, right.encode extra)))).vec := by
  apply applyVec_encoded_ket_smul_of_binaryMatrix
  change ((UnitaryCircuit.onBinaryPrefix right.width body).binaryMatrix environment).applyVec
    (NormalizedVector.ket (prodEquiv (left.encode input, right.encode extra))).vec =
      coefficient •
        (NormalizedVector.ket (prodEquiv (left.encode output, right.encode extra))).vec
  rw [← NormalizedVector.tensor_ket]
  change ((UnitaryCircuit.onBinaryPrefix right.width body).binaryMatrix environment).applyVec
    (HilbertVector.tensor (NormalizedVector.ket (left.encode input)).vec
      (NormalizedVector.ket (right.encode extra)).vec) = _
  have tensorAction := UnitaryCircuit.unitaryCircuit_onBinaryPrefix_applyVec_tensor right.width
    body (NormalizedVector.ket (left.encode input)).vec
      (NormalizedVector.ket (right.encode extra)).vec environment
  have original := binaryMatrix_applyVec_encoded_ket_smul body (left.encode input)
    (left.encode output) coefficient actual
  have tensorStep := congrArg (fun vector : HilbertVector (Qubits left.width) =>
    HilbertVector.tensor vector (NormalizedVector.ket (right.encode extra)).vec) original
  refine tensorAction.trans (tensorStep.trans ?_)
  ext index
  rw [← NormalizedVector.tensor_ket]
  change (coefficient * (NormalizedVector.ket (R := Qubits left.width)
    (left.encode output)).vec _ * (NormalizedVector.ket (R := Qubits right.width)
      (right.encode extra)).vec _) =
      coefficient * ((NormalizedVector.ket (R := Qubits left.width) (left.encode output)).vec _ *
        (NormalizedVector.ket (R := Qubits right.width) (right.encode extra)).vec _)
  exact mul_assoc _ _ _

end

end QuantumAlg.UnitaryCircuit.Realizes
