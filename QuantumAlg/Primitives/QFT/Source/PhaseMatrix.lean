/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source.Matrix
public import QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Primitive
import all QuantumAlg.Primitives.QFT.Mathematics.PhaseFactors
import all QuantumAlg.Components.Gates.ControlledPhase.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# The actual native QFT phase layer

Each native controlled-phase token has its original diagonal operator.
Composing those instructions gives the exact Fourier phase-factor product.
-/

namespace QuantumAlg.QuantumFourierTransform.Source

noncomputable section

private lemma phaseStep_binaryMatrix (oracles : OracleModel) (n : Nat) (offset : Fin n)
    (environment : oracles.Interpretation) :
    onBinaryLabels (phaseStep oracles n offset) environment =
      qftControlledPhaseOperator 0 offset.succ (phaseAngle offset.val) :=
  qftSource_primitive_binaryMatrix (environment := environment) oracles _

private lemma phasePrefix_binaryMatrix (oracles : OracleModel) (n count : Nat)
    (bounded : count ≤ n)
    (environment : oracles.Interpretation) :
    (onBinaryLabels (phasePrefix oracles n count bounded) environment : HilbertOperator (Qubits
      (n + 1))) =
      Matrix.diagonal (qftPhaseLayerFactorPrefix n count bounded) := by
  induction count with
  | zero =>
      rw [phasePrefix, qftSource_binaryMatrix_identity (environment := environment)]
      ext row column
      simp [qftPhaseLayerFactorPrefix, Matrix.one_apply, Matrix.diagonal_apply]
  | succ count ih =>
      rw [phasePrefix, qftSource_binaryMatrix_seq (environment := environment)]
      change (onBinaryLabels (phaseStep oracles n ⟨count, Nat.lt_of_succ_le bounded⟩) environment :
        HilbertOperator (Qubits (n + 1))) *
        (onBinaryLabels (phasePrefix oracles n count (Nat.le_of_succ_le bounded)) environment :
          HilbertOperator (Qubits (n + 1))) = _
      rw [phaseStep_binaryMatrix (environment := environment), ih]
      change Matrix.diagonal _ * Matrix.diagonal _ = _
      rw [Matrix.diagonal_mul_diagonal]
      rfl

/-- The full native source phase layer has the original exact Fourier phase on every input label. -/
public lemma qftSource_phase_binaryMatrix_entry (oracles : OracleModel) (n : Nat)
    (row column : (Qubits (n + 1)).Index)
    (environment : oracles.Interpretation) :
    onBinaryLabels (phaseLayer oracles n) environment row column =
      if row = column then
        (if column.val.testBit n then ω (n + 1) ^ (column.val % 2 ^ n) else 1)
      else 0 := by
  classical
  have actual := phasePrefix_binaryMatrix (environment := environment) oracles n n le_rfl
  have entry := congrArg (fun matrix : HilbertOperator (Qubits (n + 1)) =>
    matrix row column) actual
  change onBinaryLabels (phaseLayer oracles n) environment row column = _ at entry
  rw [Matrix.diagonal_apply] at entry
  by_cases same : row = column
  · subst row
    simpa only [if_pos rfl, qftPhaseLayerFactor_eq] using entry
  · simpa only [if_neg same] using entry

end

end QuantumAlg.QuantumFourierTransform.Source
