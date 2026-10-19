/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Entries
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Instrument
import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Primitives.QFT.Semiclassical.PhaseMatrix
import Mathlib.Tactic.SplitIfs

/-!
# Source Fourier rows of the actual recursive retained-bank instrument

At each literal stage the intermediate physical basis is fixed by the
measured head bit, the original tail, every complementary system and the
external reference. The finite matrix product therefore collapses to that
unique actual intermediate basis. Induction identifies the native branch
with the independently defined signed Fourier source row at every width.

The final-store theorem keeps all original storage blocks and every actual
write collision. Physical output tuples remain in their original wire order;
the existing source bridge supplies the reversed frequency labels separately.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution MeasurementInstrument
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum}

/-- Source feedback evaluated on the existing tail tuple, with the physical rotation sign. -/
def sourcePhaseWeight (inverse : Bool) (n : Nat) (bit : Fin 2) (input : Bits n) : Complex :=
  if bit = 1 then
    (if inverse then star (ω (n + 1) ^ (binaryEquiv n input).val)
      else ω (n + 1) ^ (binaryEquiv n input).val)
    else 1

/-- The independent coherent source recurrence in the unchanged physical bit order. -/
def signedSourceMatrix (inverse : Bool) (n : Nat) : Matrix (Bits n) (Bits n) Complex :=
  coherent Gate.HOp (fun width bit => Matrix.diagonal (sourcePhaseWeight inverse width bit)) n

/-- The positive recurrence is exactly the existing no-SWAP physical source operator. -/
lemma signedSourceMatrix_forward (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    signedSourceMatrix false n = sourceMatrix oracles n environment := by
  exact qftSemiclassical_coherent_eq_sourceMatrix oracles environment n

/-- Negative physical rotations conjugate the same actual source ordering. -/
lemma signedSourceMatrix_inverse (oracles : OracleModel) (n : Nat)
    (environment : oracles.Interpretation) :
    signedSourceMatrix true n = conjugate (sourceMatrix oracles n environment) := by
  have phases : (fun width bit => Matrix.diagonal (sourcePhaseWeight true width bit)) =
      fun width bit => conjugate (feedback width bit) := by
    funext width bit
    ext row column
    by_cases same : row = column <;>
      by_cases selected : bit = 1 <;>
      simp [sourcePhaseWeight, feedback, conjugate, same, selected]
  unfold signedSourceMatrix
  rw [phases, ← qftSemiclassical_hadamard_real, coherent_conjugate,
    qftSemiclassical_coherent_eq_sourceMatrix oracles environment]

/-- The source recurrence has the exact tail-times-phase-times-H scalar at each head. -/
lemma signedSourceMatrix_succ (inverse : Bool) (n : Nat)
    (outcomeHead inputHead : Fin 2) (outcomeTail inputTail : Bits n) :
    signedSourceMatrix inverse (n + 1) (outcomeHead, outcomeTail) (inputHead, inputTail) =
      signedSourceMatrix inverse n outcomeTail inputTail *
        sourcePhaseWeight inverse n outcomeHead inputTail * Gate.HOp outcomeHead inputHead := by
  exact phaseStage_entry Gate.HOp (sourcePhaseWeight inverse n)
    (signedSourceMatrix inverse n) outcomeHead inputHead outcomeTail inputTail

/-- Mathematical coordinates retain the whole physical complement and the external reference. -/
def referenceBankCoordinates {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) (Reference : Register) :
    (ctx.register.prod Reference).Index ≃ Bits n ×
      (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding wires).selection ×
        Reference.Index) :=
  (Equiv.prodCongr (bankCoordinates wires qubits) (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc _ _ _)

/-- These coordinates read existing basis values and do not allocate or move a physical system. -/
lemma referenceBankCoordinates_apply {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) (Reference : Register)
    (basis : (ctx.register.prod Reference).Index) :
    referenceBankCoordinates wires qubits Reference basis =
      ((bankCoordinates wires qubits basis.1).1,
        ((bankCoordinates wires qubits basis.1).2, basis.2)) := rfl

private lemma retained_head_tail_sum {B T R : Type} [Fintype B] [Fintype T] [Fintype R]
    (head : B) (tail : T) (amplitude phase : T → Complex) (H : B → B → Complex)
    (row column : (B × T) × R) :
    (∑ middle : (B × T) × R,
      (if row.1.2 = tail ∧ row.1.1 = middle.1.1 ∧ row.2 = middle.2
        then amplitude middle.1.2 else 0) *
      (if middle.1.1 = head ∧ middle.1.2 = column.1.2 ∧ middle.2 = column.2
        then phase middle.1.2 * H head column.1.1 else 0)) =
      if row.1 = (head, tail) ∧ row.2 = column.2 then
        amplitude column.1.2 * phase column.1.2 * H head column.1.1 else 0 := by
  rw [Finset.sum_eq_single ((head, column.1.2), column.2)]
  · by_cases tailSame : row.1.2 = tail <;> by_cases headSame : row.1.1 = head <;>
      by_cases restSame : row.2 = column.2 <;>
      simp [tailSame, headSame, restSame, Prod.ext_iff, mul_assoc]
  · intro middle _ different
    have excluded : ¬(middle.1.1 = head ∧ middle.1.2 = column.1.2 ∧
        middle.2 = column.2) := by
      rintro ⟨headSame, tailSame, restSame⟩
      exact different (Prod.ext (Prod.ext headSame tailSame) restSame)
    simp only [if_neg excluded, mul_zero]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

/-- A real stage fixes precisely the observed head, original tail and full untouched remainder. -/
lemma nativeStageKraus_coordinate_entry {environment : OracleModel.empty.Interpretation}
    (inverse : Bool) {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (Reference : Register) (bit : Fin 2) (row column : (ctx.register.prod Reference).Index) :
    let coordinates := referenceBankCoordinates wires qubits Reference
    nativeStageKraus (environment := environment) inverse (wires 0) (qubits 0) (tailPhysicalWires
      wires)
        (fun i => qubits i.succ) Reference
        (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm bit) row column =
      if (coordinates row).1.1 = bit ∧
          (coordinates row).1.2 = (coordinates column).1.2 ∧
          (coordinates row).2 = (coordinates column).2 then
        sourcePhaseWeight inverse n bit (coordinates row).1.2 *
          Gate.HOp bit (coordinates column).1.1 else 0 := by
  dsimp only
  let outcome := Fin.cast
    (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm bit
  have actualBit : outcomeBit (wires 0) (qubits 0) outcome = bit := Fin.ext rfl
  have sector := bankCoordinates_head_outcome_iff wires qubits row.1 outcome
  rw [actualBit] at sector
  dsimp only [outcome] at sector
  rw [nativeStageKraus_bank_entry, actualBit, sourceFeedbackScalar_tail_coordinates]
  simp only [referenceBankCoordinates_apply, Prod.mk.injEq, ← sector]
  by_cases headSame : (bankCoordinates wires qubits row.1).1.1 = bit <;>
    by_cases tailSame : (bankCoordinates wires qubits row.1).1.2 =
        (bankCoordinates wires qubits column.1).1.2 <;>
    by_cases complementSame : (bankCoordinates wires qubits row.1).2 =
        (bankCoordinates wires qubits column.1).2 <;>
    by_cases referenceSame : row.2 = column.2 <;>
    simp [headSame, tailSame, complementSame, referenceSame, sourcePhaseWeight]

/-- Every actual native branch is the exact source row with its physical bank retained. -/
lemma nativeOutcomeKraus_source_entry {environment : OracleModel.empty.Interpretation} (inverse
    : Bool) (Reference : Register) :
    ∀ (n : Nat) (wires : Fin n ↪ Fin ctx.systemCount)
      (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
      (outcome : Bits n) (row column : (ctx.register.prod Reference).Index),
      nativeOutcomeKraus
        (environment := environment) inverse Reference n wires qubits outcome row column =
        if (referenceBankCoordinates wires qubits Reference row).1 = outcome ∧
            (referenceBankCoordinates wires qubits Reference row).2 =
              (referenceBankCoordinates wires qubits Reference column).2 then
          signedSourceMatrix inverse n outcome
            (referenceBankCoordinates wires qubits Reference column).1 else 0 := by
  intro n
  induction n with
  | zero =>
      intro wires qubits outcome row column
      let coordinates := referenceBankCoordinates wires qubits Reference
      have equality : row = column ↔ (coordinates row).2 = (coordinates column).2 := by
        constructor
        · intro same
          rw [same]
        · intro same
          exact coordinates.injective (Prod.ext (@Subsingleton.elim Unit inferInstance _ _) same)
      have unique : (coordinates row).1 = outcome := @Subsingleton.elim Unit inferInstance _ _
      change (1 : HilbertOperator (ctx.register.prod Reference)) row column =
        if (coordinates row).1 = outcome ∧ (coordinates row).2 = (coordinates column).2
          then 1 else 0
      simp only [Matrix.one_apply, unique, true_and, equality]
  | succ n ih =>
      intro wires qubits outcome row column
      rcases outcome with ⟨head, tail⟩
      let coordinates : (ctx.register.prod Reference).Index ≃
          (Fin 2 × Bits n) ×
            (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding wires).selection ×
              Reference.Index) := referenceBankCoordinates wires qubits Reference
      have trailing (middle : (ctx.register.prod Reference).Index) :
          nativeOutcomeKraus
            (environment := environment) inverse Reference n (tailPhysicalWires wires)
            (fun i => qubits i.succ) tail row middle =
          if (coordinates row).1.2 = tail ∧
              (coordinates row).1.1 = (coordinates middle).1.1 ∧
              (coordinates row).2 = (coordinates middle).2 then
            signedSourceMatrix inverse n tail (coordinates middle).1.2 else 0 := by
        have selected (basis : (ctx.register.prod Reference).Index) :
            (referenceBankCoordinates (tailPhysicalWires wires)
              (fun i => qubits i.succ) Reference basis).1 = (coordinates basis).1.2 :=
          tailBankCoordinates_selected wires qubits basis.1
        have selectedCondition :
            (referenceBankCoordinates (tailPhysicalWires wires)
              (fun i => qubits i.succ) Reference row).1 = tail ↔
                (coordinates row).1.2 = tail :=
          Iff.of_eq (congrArg (fun input : Bits n => input = tail) (selected row))
        have remainder :
            (referenceBankCoordinates (tailPhysicalWires wires)
                (fun i => qubits i.succ) Reference row).2 =
              (referenceBankCoordinates (tailPhysicalWires wires)
                (fun i => qubits i.succ) Reference middle).2 ↔
              (coordinates row).1.1 = (coordinates middle).1.1 ∧
                (coordinates row).2 = (coordinates middle).2 := by
          change ((bankCoordinates (tailPhysicalWires wires)
              (fun i => qubits i.succ) row.1).2, row.2) =
            ((bankCoordinates (tailPhysicalWires wires)
              (fun i => qubits i.succ) middle.1).2, middle.2) ↔
              (bankCoordinates wires qubits row.1).1.1 =
                  (bankCoordinates wires qubits middle.1).1.1 ∧
                ((bankCoordinates wires qubits row.1).2, row.2) =
                  ((bankCoordinates wires qubits middle.1).2, middle.2)
          constructor
          · intro same
            have physical := congrArg Prod.fst same
            have reference := congrArg Prod.snd same
            rcases (tailBankCoordinates_complement_eq_iff
              wires qubits row.1 middle.1).mp physical with ⟨headSame, restSame⟩
            exact ⟨headSame, Prod.ext restSame reference⟩
          · rintro ⟨headSame, restSame⟩
            have reference : row.2 = middle.2 :=
              congrArg (fun pair :
                ctx.quantumLayout.ComplementBasis (physicalBankEmbedding wires).selection ×
                  Reference.Index => pair.2) restSame
            exact Prod.ext
              ((tailBankCoordinates_complement_eq_iff wires qubits row.1 middle.1).mpr
                ⟨headSame, congrArg Prod.fst restSame⟩) reference
        refine (ih (tailPhysicalWires wires) (fun i => qubits i.succ) tail row middle).trans ?_
        exact if_congr (and_congr selectedCondition remainder)
          (congrArg (fun input : Bits n => signedSourceMatrix inverse n tail input)
            (selected middle)) rfl
      rw [nativeOutcomeKraus, Matrix.mul_apply]
      have entries (middle : (ctx.register.prod Reference).Index) :=
        congrArg₂ (fun first second : Complex => first * second) (trailing middle)
          (nativeStageKraus_coordinate_entry (environment := environment)
            inverse wires qubits Reference head middle column)
      refine (Finset.sum_congr rfl (fun middle _ => entries middle)).trans ?_
      let hadamard : Matrix (Fin 2) (Fin 2) Complex := Gate.HOp
      let summand : ((Fin 2 × Bits n) ×
          (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding wires).selection ×
            Reference.Index)) → Complex := fun middle =>
        (if (coordinates row).1.2 = tail ∧
            (coordinates row).1.1 = middle.1.1 ∧ (coordinates row).2 = middle.2 then
          signedSourceMatrix inverse n tail middle.1.2 else 0) *
        (if middle.1.1 = head ∧ middle.1.2 = (coordinates column).1.2 ∧
            middle.2 = (coordinates column).2 then
          sourcePhaseWeight inverse n head middle.1.2 *
            hadamard head (coordinates column).1.1 else 0)
      change (∑ middle : (ctx.register.prod Reference).Index, summand (coordinates middle)) = _
      refine (coordinates.sum_comp summand).trans ?_
      dsimp only [summand]
      refine (Eq.trans ?_ (retained_head_tail_sum head tail
        (fun input : Bits n => signedSourceMatrix inverse n tail input)
        (sourcePhaseWeight inverse n head) (fun left right : Fin 2 => hadamard left right)
        (coordinates row) (coordinates column))).trans ?_
      · apply Finset.sum_congr rfl
        intro middle _
        apply congrArg₂ (fun first second : Complex => first * second)
        · by_cases selected : (coordinates row).1.2 = tail ∧
              (coordinates row).1.1 = middle.1.1 ∧ (coordinates row).2 = middle.2
          · simp only [if_pos selected]
          · simp only [if_neg selected]
        · by_cases selected : middle.1.1 = head ∧
              middle.1.2 = (coordinates column).1.2 ∧ middle.2 = (coordinates column).2
          · simp only [if_pos selected]
          · simp only [if_neg selected]
      · split_ifs <;> first
        | exact (signedSourceMatrix_succ inverse n head
            (coordinates column).1.1 tail (coordinates column).1.2).symm
        | rfl
        | contradiction

/-- The native operator is the existing adaptive row with its actual physical bank retained. -/
lemma nativeOutcomeKraus_adaptive_entry {environment : OracleModel.empty.Interpretation}
    (inverse : Bool) (Reference : Register) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outcome : Bits n) (row column : (ctx.register.prod Reference).Index) :
    nativeOutcomeKraus
      (environment := environment) inverse Reference n wires qubits outcome row column =
      bankKraus outcome
        (adaptiveKraus Gate.HOp
          (fun width bit => Matrix.diagonal (sourcePhaseWeight inverse width bit)) n outcome)
        (referenceBankCoordinates wires qubits Reference row)
        (referenceBankCoordinates wires qubits Reference column) := by
  rw [adaptiveKraus_eq_coherent_row, bankKraus_coherent_entry,
    nativeOutcomeKraus_source_entry]
  by_cases selected : (referenceBankCoordinates wires qubits Reference row).1 = outcome <;>
    by_cases unchanged : (referenceBankCoordinates wires qubits Reference row).2 =
        (referenceBankCoordinates wires qubits Reference column).2 <;>
    simp only [selected, unchanged, and_self, false_and, and_false,
      if_true, if_false, mul_one, mul_zero, signedSourceMatrix]

/-- Source-row operator on the complete actual physical bank, complement and reference. -/
def sourceOutcomeKraus (inverse : Bool) (Reference : Register) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outcome : Bits n) : HilbertOperator (ctx.register.prod Reference) :=
  fun row column =>
    if (referenceBankCoordinates wires qubits Reference row).1 = outcome ∧
        (referenceBankCoordinates wires qubits Reference row).2 =
          (referenceBankCoordinates wires qubits Reference column).2 then
      signedSourceMatrix inverse n outcome
        (referenceBankCoordinates wires qubits Reference column).1 else 0

/-- Full physical operator equality is derived from native instructions and source coordinates. -/
lemma nativeOutcomeKraus_eq_source {environment : OracleModel.empty.Interpretation} (inverse :
    Bool) (Reference : Register) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outcome : Bits n) :
    nativeOutcomeKraus (environment := environment) inverse Reference n wires qubits outcome =
      sourceOutcomeKraus inverse Reference n wires qubits outcome := by
  ext row column
  exact nativeOutcomeKraus_source_entry inverse Reference n wires qubits outcome row column

/-- The literal schedule has the exact source-row instrument at every actual final store. -/
lemma code_source_instrument_store_matrix {environment : (ExecutionModel.quantum
    AlgorithmGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((code inverse n wires qubits outputs).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Bits n,
        if outcomeStore wires qubits outputs original outcome = stored then
          sourceOutcomeKraus inverse Reference n wires qubits outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (sourceOutcomeKraus inverse Reference n wires qubits outcome).conjTranspose
        else 0 := by
  simpa only [nativeOutcomeKraus_eq_source] using
    code_instrument_store_matrix inverse n wires qubits outputs state stored

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
