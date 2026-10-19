/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.DecodedSchedule
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Correction.Gates

/-!
# Actual fixed shared-EEA schedule produces the original-input inverse

The actual initialization, independent fixed repetition, full-clock
inverse rotations, and retained-parity output correction execute in
that order [LYL+26, sec_EEA/sub_4phase.tex:107-128]. The resulting
little-endian Work2 value is the signed terminal coefficient and its
product with the coprime positive residue is one modulo the original
modulus, including even nontrivial moduli. This coprime domain is a project
proof extension of the source's prime domain. Modulus one needs a separate
execution branch.

The theorem is about the same composed native circuit's exact encoded
ket. Every other forward-history field remains present for the actual
adjoint. Copying the output and reversing that complete circuit are
subsequent operations, not consequences of a classical callback.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CorrectedSchedule

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NumberTheory.SharedEEA

private lemma coefficient_bound (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (TerminalPadding.finalState modulus input).previousCoefficient ≤ modulus :=
  (Capacity.iteration_fields_le _ modulus
    (TerminalPadding.final_admissible modulus input positive bounded)
    (TerminalPadding.final_balance modulus input)).2.2.2

private lemma coefficient_fits (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (TerminalPadding.finalState modulus input).previousCoefficient <
      2 ^ (modulus.size + 3) :=
  (coefficient_bound modulus input positive bounded).trans_lt
    ((Nat.lt_size_self modulus).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega)))

/-- The actual decoded word, read in its physical orientation, contains the entire coefficient. -/
lemma decoded_word (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (DecodedSchedule.result modulus input positive bounded).secondWord.reverse =
      BitVec.ofNat (modulus.size + 3)
        (TerminalPadding.finalState modulus input).previousCoefficient := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  rw [BitVec.getLsbD_reverse,
    DecodedSchedule.result_coefficient_bit modulus input index positive bounded within]
  simp only [BitVec.getLsbD_ofNat, within, decide_true, Bool.true_and]

private lemma decoded_value (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (DecodedSchedule.result modulus input positive bounded).secondWord.reverse.toNat =
      (TerminalPadding.finalState modulus input).previousCoefficient := by
  rw [decoded_word, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (coefficient_fits modulus input positive bounded)]

/-- Execute the same fixed forward schedule, physical decoder, and actual output reflection. -/
def program (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum :=
  (DecodedSchedule.program modulus nontrivial).seq (OutputCorrection.nativeProgram modulus)

/-- The complete corrected physical frame keeps every non-output part of the forward history. -/
def result (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    Registers modulus.size :=
  OutputCorrection.step modulus (DecodedSchedule.result modulus input positive bounded)

/-- The exact normalized-basis action of the full actual circuit on every coprime positive input. -/
lemma program_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
            ((encoding modulus.size).encode (InitialFrame.initial modulus input)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding modulus.size).width).basisEquiv.symm
          ((encoding modulus.size).encode (result modulus input.val positive bounded))) := by
  rw [program, UnitaryCircuit.applyNormalized_seq,
    DecodedSchedule.program_initial modulus nontrivial input coprime positive bounded,
    (OutputCorrection.outputCorrection_nativeProgram_realizes modulus).apply_encoded_ket]
  rfl

/-- The actual Work2 value is precisely the original-input signed terminal coefficient. -/
lemma result_value (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    (result modulus input positive bounded).secondWord.reverse.toNat =
      SignedInvariant.output modulus (TerminalPadding.finalState modulus input)
        (SignedTrajectory.finalIteration modulus input) := by
  have fitted : (DecodedSchedule.result modulus input positive bounded).secondWord.reverse.toNat ≤
      modulus := by
    rw [decoded_value]
    exact coefficient_bound modulus input positive bounded
  rw [result, OutputCorrection.step_value modulus _ fitted, decoded_value,
    DecodedSchedule.result_iteration]
  rfl

/-- The actual output value is a multiplicative inverse on the coprime positive-residue domain. -/
lemma result_product (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    (input : ZMod modulus) *
      ((result modulus input positive bounded).secondWord.reverse.toNat : ZMod modulus) = 1 := by
  rw [result_value]
  exact SignedTrajectory.final_product modulus input coprime positive bounded

/-- The actual corrected value fits the original n-bit output word without a new fit promise. -/
lemma result_fits_output (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (result modulus input positive bounded).secondWord.reverse.toNat < 2 ^ modulus.size := by
  rw [result_value]
  have coefficient := coefficient_bound modulus input positive bounded
  apply lt_of_le_of_lt _ (Nat.lt_size_self modulus)
  unfold SignedInvariant.output
  split
  · exact coefficient
  · exact Nat.sub_le _ _

/-- All original controls, lengths, and first-word history survive the actual output correction. -/
lemma result_retained (modulus input : Nat) (positive : 0 < input) (bounded : input < modulus) :
    let before := DecodedSchedule.result modulus input positive bounded
    let after := result modulus input positive bounded
    after.firstWord = before.firstWord ∧
      after.coefficientLength = before.coefficientLength ∧
      after.quotientLength = before.quotientLength ∧
      after.divisorLength = before.divisorLength ∧
      after.shift = before.shift ∧ after.flags = before.flags ∧ after.control = before.control :=
  OutputCorrection.step_retained modulus _

/-- The same complete forward circuit is reversed; no part of Gamma is discarded. -/
lemma dagger_after_forward (modulus : Nat) (nontrivial : 1 < modulus)
    (state : NormalizedVector
      (QubitLayout.canonical (encoding modulus.size).width).toQuantum.register) :
    ((program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
        ((program modulus nontrivial).applyNormalized environment state) =
      state :=
  UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized (program modulus nontrivial)
    ((program modulus nontrivial).dagger (AlgorithmGate.oracleFreeAdjoints .empty))
    (by rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]; exact Unitary.star_eq_inv _) state

end

end QuantumAlg.MAU.Inversion.SharedEEA.CorrectedSchedule
