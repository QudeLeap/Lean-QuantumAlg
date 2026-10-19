/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Program
import all QuantumAlg.Util.NumberTheory.SharedEEA.CanonicalInverse

/-!
# Exact modular addition with complete shared-EEA history restoration

The corrected forward coefficient is the canonical inverse on the unit
domain. The actual middle program preserves every computed field while
adding into any canonical target. Reversing the same complete forward
therefore restores its entire initial frame. The unit-facing theorem
derives all nontrivial EEA side conditions internally. Modulus one and
actual fixed auxiliary preparation belong to the subsequent runtime layer.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Accumulate

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NumberTheory.SharedEEA

/-- Read the complete corrected inverse using the physical Work2 orientation. -/
lemma accumulateCorrected_value (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) :
    OutputCopy.value (CorrectedSchedule.result modulus input positive bounded) =
      CanonicalInverse.word modulus (positive.trans bounded) input := by
  have source : OutputCopy.value (CorrectedSchedule.result modulus input positive bounded) =
      InverseOutput.word modulus input positive bounded := by
    apply Fin.ext
    rw [OutputCopy.value_of_fits _
      (CorrectedSchedule.result_fits_output modulus input positive bounded),
      CorrectedSchedule.result_value]
    rfl
  exact source.trans (CanonicalInverse.source_eq_word modulus input coprime positive bounded)

/-- Independent modular addition of the canonical mathematical inverse into an arbitrary target. -/
def output (modulus : Nat) (modulusPositive : 0 < modulus) (input : Nat)
    (target : Fin (2 ^ modulus.size)) : Fin (2 ^ modulus.size) :=
  ⟨(target.val + (CanonicalInverse.word modulus modulusPositive input).val) % modulus,
    (Nat.mod_lt _ modulusPositive).trans (Nat.lt_size_self modulus)⟩

/-- The actual program restores every initial EEA field and adds into any canonical target. -/
lemma accumulateProgram_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (input target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (targetBounded : target.val < modulus) :
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (InitialFrame.initial modulus input, target)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode
            (InitialFrame.initial modulus input, output modulus (by omega) input.val target))) := by
  let initial := InitialFrame.initial modulus input
  let computed := CorrectedSchedule.result modulus input.val positive bounded
  let result := output modulus (by omega) input.val target
  have forward (value : Fin (2 ^ modulus.size)) :
      (forwardProgram modulus nontrivial).applyNormalized environment
          (NormalizedVector.ket
            ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
              ((frameEncoding modulus.size).encode (initial, value)))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (computed, value))) :=
    UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
      (SharedEEA.encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
      (CorrectedSchedule.program modulus nontrivial) initial computed value
      (CorrectedSchedule.program_initial modulus nontrivial input coprime positive bounded)
  have accumulated :
      (middleProgram modulus.size (fittedModulus modulus)).applyNormalized environment
          (NormalizedVector.ket
            ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
              ((frameEncoding modulus.size).encode (computed, target)))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (computed, result))) := by
    rw [(accumulateMiddle_realizes modulus.size (fittedModulus modulus)).apply_encoded_ket]
    have fields : middleStep modulus.size (fittedModulus modulus) (computed, target) =
        (computed, result) := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        rw [accumulateMiddle_target modulus.size (fittedModulus modulus)
          (computed, target) targetBounded]
        change (target.val + (OutputCopy.value computed).val) % modulus = _
        rw [accumulateCorrected_value modulus input.val coprime positive bounded]
        rfl
    rw [fields]
  have restored :
      ((forwardProgram modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment
          (NormalizedVector.ket
            ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
              ((frameEncoding modulus.size).encode (computed, result)))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (initial, result))) :=
    (congrArg (fun state => ((forwardProgram modulus nontrivial).dagger
        (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment state)
      (forward result)).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
        (forwardProgram modulus nontrivial)
        ((forwardProgram modulus nontrivial).dagger
          (AlgorithmGate.oracleFreeAdjoints .empty))
        (by rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]; exact Unitary.star_eq_inv _)
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (initial, result)))))
  exact UnitaryCircuit.applyNormalized_seq_of_eq (forward target)
    (UnitaryCircuit.applyNormalized_seq_of_eq accumulated restored)

/-- Canonically encode every modular residue at the original modulus width. -/
def residueWord (modulus : Nat) (modulusPositive : 0 < modulus) (value : ZMod modulus) :
    Fin (2 ^ modulus.size) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  exact ⟨value.val, (ZMod.val_lt value).trans (Nat.lt_size_self modulus)⟩

/-- Original units and arbitrary modular targets require no additional residue or width promises. -/
lemma accumulateProgram_unit (modulus : Nat) (nontrivial : 1 < modulus)
    (input : (ZMod modulus)ˣ) (target : ZMod modulus) :
    let inputWord := residueWord modulus (by omega) (input : ZMod modulus)
    let targetWord := residueWord modulus (by omega) target
    (program modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
            ((frameEncoding modulus.size).encode (InitialFrame.initial modulus inputWord,
              targetWord)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (frameEncoding modulus.size).width).basisEquiv.symm
          ((frameEncoding modulus.size).encode (InitialFrame.initial modulus inputWord,
            output modulus (by omega) inputWord.val targetWord))) := by
  let : NeZero modulus := ⟨by omega⟩
  obtain ⟨positive, bounded, coprime, _⟩ :=
    CanonicalInverse.unit_input_conditions modulus nontrivial input
  exact accumulateProgram_initial modulus nontrivial _ _ coprime positive bounded
    (ZMod.val_lt target)

/-- Arbitrary supplied encoded fields, including a live flag, survive with the full frame. -/
lemma accumulateProgram_reference {Reference : Type} (reference : BinaryLabelEncoding Reference)
    (modulus : Nat) (nontrivial : 1 < modulus)
    (input target : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (targetBounded : target.val < modulus) (retained : Reference) :
    (UnitaryCircuit.onBinaryPrefix reference.width (program modulus nontrivial)).applyNormalized
      environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (BinaryLabelEncoding.prod (frameEncoding modulus.size) reference).width).basisEquiv.symm
            ((BinaryLabelEncoding.prod (frameEncoding modulus.size) reference).encode
              ((InitialFrame.initial modulus input, target), retained)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (BinaryLabelEncoding.prod (frameEncoding modulus.size) reference).width).basisEquiv.symm
          ((BinaryLabelEncoding.prod (frameEncoding modulus.size) reference).encode
            ((InitialFrame.initial modulus input,
              output modulus (by omega) input.val target), retained))) :=
  UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (frameEncoding modulus.size) reference (program modulus nontrivial) _ _ retained
    (accumulateProgram_initial modulus nontrivial input target coprime positive bounded
      targetBounded)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Accumulate
