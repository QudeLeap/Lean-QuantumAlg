/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Correctness
import all QuantumAlg.Util.NumberTheory.SharedEEA.CanonicalInverse

/-!
# Exact quotient accumulation with complete shared-EEA history restoration

The corrected forward coefficient is the canonical inverse on the unit
domain. The actual middle program preserves every computed field while
adding inverse times the unchanged numerator into any canonical target.
Reversing the same complete forward restores its entire initial frame. The unit-facing theorem
derives all nontrivial EEA side conditions internally. Modulus one and
actual fixed auxiliary preparation belong to the subsequent runtime layer.
-/

namespace QuantumAlg.MAU.Division.SharedEEA

noncomputable section

open NumberTheory.SharedEEA
open Inversion.SharedEEA

/-- Independent quotient accumulation using the canonical mathematical inverse. -/
def output (modulus : Nat) (modulusPositive : 0 < modulus) (input : Nat)
    (numerator target : Fin (2 ^ modulus.size)) : Fin (2 ^ modulus.size) :=
  ⟨(target.val +
      (CanonicalInverse.word modulus modulusPositive input).val * numerator.val) % modulus,
    (Nat.mod_lt _ modulusPositive).trans (Nat.lt_size_self modulus)⟩

/-- Restore every EEA field and accumulate the quotient into any canonical target. -/
theorem divisionProgram_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input numerator target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (targetBounded : target.val < modulus) :
    (program modulus nontrivial).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode
            (InitialFrame.initial modulus input, numerator, target))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode
          (InitialFrame.initial modulus input, numerator,
            output modulus (by omega) input.val numerator target)) := by
  let initial := InitialFrame.initial modulus input
  let computed := CorrectedSchedule.result modulus input.val positive bounded
  let result := output modulus (by omega) input.val numerator target
  have forward (value : Fin (2 ^ modulus.size)) :
      (forwardProgram modulus nontrivial).applyNormalized
          (NormalizedVector.ket ((frameEncoding modulus.size).encode (initial, numerator, value))) =
        NormalizedVector.ket ((frameEncoding modulus.size).encode (computed, numerator, value)) :=
    UnitaryCircuit.Realizes.prodLeft_applyNormalized_encoded_ket_of_eq
      (Inversion.SharedEEA.encoding modulus.size)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity modulus.size)
        (BinaryLabelEncoding.finIdentity modulus.size))
      (CorrectedSchedule.program modulus nontrivial) initial computed (numerator, value)
      (CorrectedSchedule.program_initial modulus nontrivial input coprime positive bounded)
  have accumulated :
      (middleProgram modulus.size (Accumulate.fittedModulus modulus)).applyNormalized
          (NormalizedVector.ket
            ((frameEncoding modulus.size).encode (computed, numerator, target))) =
        NormalizedVector.ket
          ((frameEncoding modulus.size).encode (computed, numerator, result)) := by
    rw [(divisionMiddle_realizes modulus.size (Accumulate.fittedModulus modulus)).apply_encoded_ket]
    have fields : middleStep modulus.size (Accumulate.fittedModulus modulus)
        (computed, numerator, target) =
        (computed, numerator, result) := by
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Fin.ext
          rw [divisionMiddle_target modulus.size (Accumulate.fittedModulus modulus)
            (computed, numerator, target) targetBounded]
          change (target.val + (OutputCopy.value computed).val * numerator.val) % modulus = _
          rw [Accumulate.accumulateCorrected_value modulus input.val coprime positive bounded]
          rfl
    rw [fields]
  have restored :
      (forwardProgram modulus nontrivial).dagger.applyNormalized
          (NormalizedVector.ket
            ((frameEncoding modulus.size).encode (computed, numerator, result))) =
        NormalizedVector.ket ((frameEncoding modulus.size).encode (initial, numerator, result)) :=
    (congrArg (forwardProgram modulus nontrivial).dagger.applyNormalized
      (forward result)).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
        (forwardProgram modulus nontrivial)
        (NormalizedVector.ket ((frameEncoding modulus.size).encode (initial, numerator, result))))
  exact UnitaryCircuit.applyNormalized_seq_of_eq (forward target)
    (UnitaryCircuit.applyNormalized_seq_of_eq accumulated restored)

/-- Original units, arbitrary numerators and targets require no additional residue promises. -/
theorem divisionProgram_unit (modulus : Nat) (nontrivial : 1 < modulus)
    (input : (ZMod modulus)ˣ) (numerator target : ZMod modulus) :
    let inputWord := Accumulate.residueWord modulus (by omega) (input : ZMod modulus)
    let numeratorWord := Accumulate.residueWord modulus (by omega) numerator
    let targetWord := Accumulate.residueWord modulus (by omega) target
    (program modulus nontrivial).applyNormalized
        (NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
          ((frameEncoding modulus.size).encode (InitialFrame.initial modulus inputWord,
            numeratorWord, targetWord))) =
      NormalizedVector.ket (R := Qubits (frameEncoding modulus.size).width)
        ((frameEncoding modulus.size).encode (InitialFrame.initial modulus inputWord, numeratorWord,
          output modulus (by omega) inputWord.val numeratorWord targetWord)) := by
  let : NeZero modulus := ⟨by omega⟩
  obtain ⟨positive, bounded, coprime, _⟩ :=
    CanonicalInverse.unit_input_conditions modulus nontrivial input
  exact divisionProgram_initial modulus nontrivial _ _ _ coprime positive bounded
    (ZMod.val_lt target)

/-- Arbitrary supplied encoded fields, including a live flag, survive with the full frame. -/
theorem divisionProgram_reference {Reference : Type} (reference : BinaryLabelEncoding Reference)
    (modulus : Nat) (nontrivial : 1 < modulus)
    (input numerator target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (targetBounded : target.val < modulus) (retained : Reference) :
    (UnitaryCircuit.prodLeft (n := reference.width) (program modulus nontrivial)).applyNormalized
        (NormalizedVector.ket
          ((BinaryLabelEncoding.prod (frameEncoding modulus.size) reference).encode
            ((InitialFrame.initial modulus input, numerator, target), retained))) =
      NormalizedVector.ket
        ((BinaryLabelEncoding.prod (frameEncoding modulus.size) reference).encode
          ((InitialFrame.initial modulus input, numerator,
            output modulus (by omega) input.val numerator target), retained)) :=
  UnitaryCircuit.Realizes.prodLeft_applyNormalized_encoded_ket_of_eq
    (frameEncoding modulus.size) reference (program modulus nontrivial) _ _ retained
    (divisionProgram_initial modulus nontrivial input numerator target coprime positive bounded
      targetBounded)

end

end QuantumAlg.MAU.Division.SharedEEA
