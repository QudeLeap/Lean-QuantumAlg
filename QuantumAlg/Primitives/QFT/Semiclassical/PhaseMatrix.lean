/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Construction
public import QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Core.Base.Gate.Placement.Diagonal
import all QuantumAlg.Core.Base.Gate.Placement.Construction
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.PhaseOperator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Util.Complex
import Mathlib.Tactic.FinCases

/-!
# Full-layout matrix of the actual feedback phase word

The diagonal weights are read from the native one-qubit tokens at their actual
wire positions. Every complementary quantum coordinate is retained, and the
prefix identity follows the literal sequential composition of those gates.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

open QuantumAlg.MeasurementInstrument

noncomputable section

private lemma phase_token_diagonal (angle : Real) :
    ((AlgorithmGate.model.operator (.singleQubit (phaseGateOp angle))).val :
      HilbertOperator (QuantumSignature.qubits 1).register) =
        Matrix.diagonal (fun basis =>
          if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else
            Complex.exp ((angle : Complex) * Complex.I)) := by
  ext row column
  change (phaseGateOp angle : HilbertOperator (Qubits 1))
    (QuantumSignature.qubitsIndexEquiv 1 row)
      (QuantumSignature.qubitsIndexEquiv 1 column) = _
  rw [phaseGateOp_diagonal]
  simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]

/-- One native phase token has exactly its selected-wire diagonal on the complete layout. -/
public lemma qftSemiclassical_nativePhase_diagonal {count : Nat}
    (layout : QuantumLayout count) (angle : Real) (target : Fin count)
    (qubit : (layout.wire target).dimension = 2) {environment : OracleModel.empty.Interpretation} :
    (((Gate.singleQubitAt layout .empty (phaseGateOp angle) target qubit).matrix environment) :
      HilbertOperator layout.register) =
        Matrix.diagonal (fun basis => if (basis target).val = 0 then 1 else
          Complex.exp ((angle : Complex) * Complex.I)) := by
  let application := Gate.singleQubitApplication layout (phaseGateOp angle) target qubit
  have selected (basis : layout.Basis) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 =
        Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) := by
    have coordinates : (application.basisEquiv basis).1 =
        fun _ => Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit) (basis target) := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) qubit)
      (basis target) = bit
    fin_cases bit <;> rfl
  have actual := application.application_operator_diagonal
    (fun basis => if QuantumSignature.qubitsIndexEquiv 1 basis = 0 then 1 else
      Complex.exp ((angle : Complex) * Complex.I)) (phase_token_diagonal angle)
  refine actual.trans ?_
  apply congrArg Matrix.diagonal
  funext basis
  have selected_value :
      (QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1).val =
        (basis target).val := congrArg Fin.val (selected basis)
  have zero_iff :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 = 0 ↔
        (basis target).val = 0 := by
    constructor
    · intro equal
      exact selected_value.symm.trans (congrArg Fin.val equal)
    · intro equal
      exact Fin.ext (selected_value.trans equal)
  exact if_congr zero_iff rfl rfl

variable {ctx : RuntimeCtx .quantum}

/-- The exact scalar accumulated by the real prefix of selected one-qubit phases. -/
public def phaseFactorPrefix (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount) :
    (count : Nat) → count ≤ n → ctx.quantumLayout.Basis → Complex
  | 0, _, _ => 1
  | count + 1, bounded, basis =>
      (if (basis (wires ⟨count, Nat.lt_of_succ_le bounded⟩)).val = 0 then 1 else
        Complex.exp ((signedPhaseAngle inverse count : Complex) * Complex.I)) *
          phaseFactorPrefix inverse wires count (Nat.le_of_succ_le bounded) basis

/-- The genuine sequential phase word equals its complete exact diagonal matrix. -/
public lemma qftSemiclassical_phasePrefix_matrix (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (count : Nat) (bounded : count ≤ n) {environment : OracleModel.empty.Interpretation} :
    (((phasePrefix inverse wires qubits count bounded).matrix environment) :
      HilbertOperator ctx.quantumLayout.register) =
        Matrix.diagonal (phaseFactorPrefix inverse wires count bounded) := by
  induction count with
  | zero =>
      rw [phasePrefix, UnitaryCircuit.identity_matrix]
      ext row column
      simp [phaseFactorPrefix, Matrix.one_apply, Matrix.diagonal_apply]
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.seq_matrix]
      change (((Gate.singleQubitAt ctx.quantumLayout .empty
          (phaseGateOp (signedPhaseAngle inverse count))
          (wires ⟨count, Nat.lt_of_succ_le bounded⟩)
          (qubits ⟨count, Nat.lt_of_succ_le bounded⟩)).matrix environment) :
          HilbertOperator ctx.quantumLayout.register) *
        (((phasePrefix inverse wires qubits count (Nat.le_of_succ_le bounded)).matrix environment) :
          HilbertOperator ctx.quantumLayout.register) = _
      rw [qftSemiclassical_nativePhase_diagonal, ih, Matrix.diagonal_mul_diagonal]
      rfl

/-- The physical Hadamard is unchanged by entrywise conjugation. -/
public lemma qftSemiclassical_hadamard_real :
    conjugate (Gate.HOp : HilbertOperator (Qubits 1)) = Gate.HOp := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [conjugate, Gate.HOp, NormalizedVector.star_invSqrt2]

/-- A negative physical phase angle is exact entrywise conjugation of the positive gate. -/
public lemma qftSemiclassical_phaseGate_negative (angle : Real) :
    (phaseGateOp (-angle) : HilbertOperator (Qubits 1)) =
      conjugate (phaseGateOp angle : HilbertOperator (Qubits 1)) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [phaseGateOp, conjugate, conj_exp_I]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
