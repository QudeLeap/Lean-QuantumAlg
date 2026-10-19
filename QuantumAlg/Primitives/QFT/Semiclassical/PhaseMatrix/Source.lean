/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.PhaseMatrix
public import QuantumAlg.Primitives.QFT.Mathematics
public import QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Primitives.QFT.Semiclassical.PhaseMatrix
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Primitives.QFT.Mathematics.PhaseFactors
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.Complex
import Mathlib.Tactic.FinCases

/-!
# Native feedback phases in the source Fourier coordinates

The actual phase prefix is identified with the existing source phase-factor
prefix by reading the selected physical tail wires in big-endian order.
Negative rotations conjugate the same ordered prefix. The resulting matrix
equation retains every complementary physical coordinate; it does not perform
a wire permutation, allocate a register, or change any classical cell.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

variable {ctx : RuntimeCtx .quantum}

/-- The existing physical tail bits expressed in the source big-endian labels. -/
public def physicalTailLabel {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.quantumLayout.Basis) : Fin (2 ^ n) :=
  BinaryBasis.bigEndianEquiv n (fun index =>
    Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits index))
      (basis (wires index)))

/-- Every encoded tail bit is the actual value at its selected physical wire. -/
public lemma qftSemiclassical_physicalTailLabel_bit {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (basis : ctx.quantumLayout.Basis) (index : Fin n) :
    (basis (wires index)).val =
      ((physicalTailLabel wires qubits basis).val.testBit (Fin.rev index).val).toNat := by
  unfold physicalTailLabel
  rw [BinaryBasis.bigEndianEquiv_bit]
  let bit : Fin 2 :=
    Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits index))
      (basis (wires index))
  change bit.val = (finTwoEquiv bit).toNat
  have encoded (value : Fin 2) : value.val = (finTwoEquiv value).toNat := by
    fin_cases value <;> rfl
  exact encoded bit

private lemma positivePhaseFactor_eq_source {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount) (basis : ctx.quantumLayout.Basis)
    (label : Fin (2 ^ n))
    (coordinates : ∀ index : Fin n,
      (basis (wires index)).val = (label.val.testBit (Fin.rev index).val).toNat)
    (offset : Fin n) :
    (if (basis (wires offset)).val = 0 then 1 else
      Complex.exp ((Source.phaseAngle offset.val : Complex) * Complex.I)) =
      qftPhaseFactorAt n offset (qftPairEquiv n (1, label)) := by
  rw [qftPhaseFactorAt_eq_omega_pow, qftPairEquiv_testBit_high,
    qftPairEquiv_testBit_low, coordinates offset]
  have angle : Complex.exp ((Source.phaseAngle offset.val : Complex) * Complex.I) =
      ω (n + 1) ^ (2 ^ (Fin.rev offset).val) := by
    simpa only [Source.phaseAngle, qftPhaseAngle] using
      qftPhaseAngle_exp_eq_omega_pow n offset
  cases label.val.testBit (Fin.rev offset).val <;> simp [angle]

/-- Each literal positive prefix equals the already proved source scalar prefix. -/
lemma qftSemiclassical_phaseFactorPrefix_source {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount) (basis : ctx.quantumLayout.Basis)
    (label : Fin (2 ^ n))
    (coordinates : ∀ index : Fin n,
      (basis (wires index)).val = (label.val.testBit (Fin.rev index).val).toNat)
    (count : Nat) (bounded : count ≤ n) :
    phaseFactorPrefix false wires count bounded basis =
      qftPhaseLayerFactorPrefix n count bounded (qftPairEquiv n (1, label)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [phaseFactorPrefix, qftPhaseLayerFactorPrefix, ih]
      apply congrArg (fun factor => factor *
        qftPhaseLayerFactorPrefix n count (Nat.le_of_succ_le bounded)
          (qftPairEquiv n (1, label)))
      simpa [signedPhaseAngle, qftPhaseFactorAt] using
        positivePhaseFactor_eq_source wires basis label coordinates
          ⟨count, Nat.lt_of_succ_le bounded⟩

/-- Sign reversal conjugates the same ordered native scalar prefix. -/
lemma qftSemiclassical_phaseFactorPrefix_negative {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount) (basis : ctx.quantumLayout.Basis)
    (count : Nat) (bounded : count ≤ n) :
    phaseFactorPrefix true wires count bounded basis =
      star (phaseFactorPrefix false wires count bounded basis) := by
  induction count with
  | zero => simp [phaseFactorPrefix]
  | succ count ih =>
      rw [phaseFactorPrefix, phaseFactorPrefix, ih]
      simp only [Complex.star_def, map_mul]
      apply congrArg (fun factor => factor *
        star (phaseFactorPrefix false wires count (Nat.le_of_succ_le bounded) basis))
      by_cases zero : (basis (wires ⟨count, Nat.lt_of_succ_le bounded⟩)).val = 0
      · simp [zero]
      · simp [zero, signedPhaseAngle, conj_exp_I]

/-- The full native feedback prefix has the source Fourier phase, with either sign. -/
public lemma qftSemiclassical_phaseFactorPrefix_eq_fourier (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount) (basis : ctx.quantumLayout.Basis)
    (label : Fin (2 ^ n))
    (coordinates : ∀ index : Fin n,
      (basis (wires index)).val = (label.val.testBit (Fin.rev index).val).toNat) :
    phaseFactorPrefix inverse wires n le_rfl basis =
      if inverse then star (ω (n + 1) ^ label.val) else ω (n + 1) ^ label.val := by
  have positive : phaseFactorPrefix false wires n le_rfl basis =
      ω (n + 1) ^ label.val := by
    rw [qftSemiclassical_phaseFactorPrefix_source wires basis label coordinates,
      qftPhaseLayerFactor_eq, qftPairEquiv_testBit_high, qftPairEquiv_mod_tail]
    simp
  cases inverse
  · exact positive
  · exact (qftSemiclassical_phaseFactorPrefix_negative wires basis n le_rfl).trans
      (congrArg star positive)

/-- Stored feedback has its source phase on the complete actual physical layout. -/
public lemma qftSemiclassical_selectedPhase_matrix_entry (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (bit : Fin 2) (row column : ctx.quantumLayout.Basis) {environment :
      OracleModel.empty.Interpretation} :
    ((selectedPhase inverse wires qubits (dimension := 2) (.finite bit)).matrix environment) row
      column =
      if row = column then
        (if bit = 1 then
          (if inverse then star (ω (n + 1) ^ (physicalTailLabel wires qubits column).val)
            else ω (n + 1) ^ (physicalTailLabel wires qubits column).val)
        else 1)
      else 0 := by
  classical
  have phase := qftSemiclassical_phaseFactorPrefix_eq_fourier inverse wires column
    (physicalTailLabel wires qubits column)
    (qftSemiclassical_physicalTailLabel_bit wires qubits column)
  fin_cases bit
  · change (((UnitaryCircuit.identity AlgorithmGate.model .empty ctx.quantumLayout).matrix
    environment) :
      HilbertOperator ctx.quantumLayout.register) row column =
        if row = column then 1 else 0
    rw [UnitaryCircuit.identity_matrix]
    exact Matrix.one_apply
  · change (((phasePrefix inverse wires qubits n le_rfl).matrix environment) :
      HilbertOperator ctx.quantumLayout.register) row column =
        if row = column then
          (if inverse then star (ω (n + 1) ^ (physicalTailLabel wires qubits column).val)
            else ω (n + 1) ^ (physicalTailLabel wires qubits column).val)
        else 0
    rw [qftSemiclassical_phasePrefix_matrix, Matrix.diagonal_apply]
    by_cases same : row = column
    · subst row
      simpa using phase
    · simp only [if_neg same]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
