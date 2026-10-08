/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Query.Complement
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
import all QuantumAlg.Algorithms.QPE.Query.Complement
import all QuantumAlg.Algorithms.QPE.Query.Coordinates
import all QuantumAlg.Algorithms.QPE.Query
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Components.Control.Entries
import all QuantumAlg.Core.Base.Oracle.Placement.Entries
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Powers
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Exact controlled-bit matrices of actual QPE source queries

The declared controlled query at each actual phase wire has the original
controlled-bit matrix on the complete phase/source register. Repeating the
query gives the source's corresponding binary power, including all phases
[Lin22, phaseestimation.tex:514-523].
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

private theorem query_pair_entry (gates : GateModel) {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth)
    (leftPhase rightPhase : Fin (2 ^ phaseWidth))
    (leftSource rightSource : Fin (2 ^ systemWidth)) :
    (sourceQuery gates unitary stage).binaryMatrix (prodEquiv (leftPhase, leftSource))
      (prodEquiv (rightPhase, rightSource)) =
      UnitaryOperator.controlledQubits unitary
        (prodEquiv (finTwoEquiv.symm (leftPhase.val.testBit stage.val), leftSource))
        (prodEquiv (finTwoEquiv.symm (rightPhase.val.testBit stage.val), rightSource)) *
        (if ((queryApplication unitary stage).basisEquiv (pairBasis leftPhase leftSource)).2 =
          ((queryApplication unitary stage).basisEquiv (pairBasis rightPhase rightSource)).2
            then 1 else 0) := by
  change (queryApplication unitary stage).operator (pairBasis leftPhase leftSource)
    (pairBasis rightPhase rightSource) = _
  rw [OracleModel.Application.oracleApplication_model_entry,
    qpeNative_query_selected_binary, qpeNative_query_selected_binary]
  change UnitaryOperator.controlledQubits unitary
    ((QuantumSignature.qubitsIndexEquiv (1 + systemWidth))
      ((QuantumSignature.qubitsIndexEquiv (1 + systemWidth)).symm
        (prodEquiv (finTwoEquiv.symm (leftPhase.val.testBit stage.val), leftSource))))
    ((QuantumSignature.qubitsIndexEquiv (1 + systemWidth))
      ((QuantumSignature.qubitsIndexEquiv (1 + systemWidth)).symm
        (prodEquiv (finTwoEquiv.symm (rightPhase.val.testBit stage.val), rightSource)))) * _ = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The actual granted query acts exactly as the original controlled-bit source operator. -/
theorem qpeNative_sourceQuery_binaryMatrix (gates : GateModel) {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth) :
    (sourceQuery gates unitary stage).binaryMatrix =
      qpeControlledBitOp phaseWidth unitary stage := by
  ext row column
  rcases (prodEquiv (m := phaseWidth) (n := systemWidth)).surjective row with
    ⟨⟨leftPhase, leftSource⟩, rfl⟩
  rcases (prodEquiv (m := phaseWidth) (n := systemWidth)).surjective column with
    ⟨⟨rightPhase, rightSource⟩, rfl⟩
  rw [query_pair_entry, UnitaryOperator.controlledQubits_pair_entry,
    qpeControlledBitOp, qpeExponentOp_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases same : leftPhase = rightPhase
  · subst rightPhase
    have complement := qpeNative_query_complement_same_phase unitary stage
      leftPhase leftSource rightSource
    simp only [complement, ↓reduceIte, mul_one]
    cases leftPhase.val.testBit stage.val <;> simp [finTwoEquiv, Matrix.one_apply]
  · rw [if_neg same]
    by_cases control : finTwoEquiv.symm (leftPhase.val.testBit stage.val) =
        finTwoEquiv.symm (rightPhase.val.testBit stage.val)
    · have complement :
          ((queryApplication unitary stage).basisEquiv (pairBasis leftPhase leftSource)).2 ≠
            ((queryApplication unitary stage).basisEquiv (pairBasis rightPhase rightSource)).2 :=
        fun equality => same (qpeNative_control_complement_phase_eq unitary stage
          leftPhase rightPhase leftSource rightSource control equality)
      rw [if_neg complement, mul_zero]
    · rw [if_neg control, zero_mul]

/-- Actual repeated source queries implement the original binary-stage exponent pointwise. -/
theorem qpeNative_powerStage_binaryMatrix (gates : GateModel) {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth) :
    (powerStage gates unitary stage).binaryMatrix =
      qpeExponentOp phaseWidth unitary
        (fun phase => 2 ^ stage.val * (phase.val.testBit stage.val).toNat) := by
  rw [powerStage, UnitaryCircuit.unitaryCircuit_binaryMatrix_iterate,
    qpeNative_sourceQuery_binaryMatrix, qpeControlledBitOp, qpeExponentOp_pow]

end

end QuantumAlg.QuantumPhaseEstimation.Native
