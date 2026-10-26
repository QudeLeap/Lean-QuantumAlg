/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Canonical
import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier.Reference.Composition
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency

/-!
# Original paid feedback products are the shared complete Fourier contraction

The comparison reuses the shared coherent-partner Fourier theorem. Original
power addresses and chronological bit positions are retained exactly; no
quantum or classical program is substituted by this source identity
[GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open QuantumFourierTransform.Semiclassical

private lemma selectedScalar_rotation (inverse : Bool) (separation : Nat) (bit : Fin 2) :
    Recycling.FeedbackCarrier.selectedScalar inverse separation (.finite bit) =
      if bit = 1 then Partner.rotation inverse separation else 1 := by
  change Complex.exp (((if bit.val = 1 then
    if inverse then -(QuantumFourierTransform.Source.phaseAngle separation)
    else QuantumFourierTransform.Source.phaseAngle separation else 0 : ℝ) : ℂ) * Complex.I) = _
  fin_cases bit <;> cases inverse <;> simp [Partner.rotation]

private lemma fourier_reference_product {Local : Register}
    (first second : HilbertOperator Local) (Reference : Register) :
    sourceWithReference (first * second) Reference =
      sourceWithReference first Reference * sourceWithReference second Reference := by
  simpa only [sourceWithReference_kronecker, Matrix.one_mul] using
    (Matrix.mul_kronecker_mul first second (1 : HilbertOperator Reference)
      (1 : HilbertOperator Reference))

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]
  (unit : (ZMod modulus.toNat)ˣ) {bits : Nat}

/-- The original MSB-addressed unitary power family of one exponent. -/
def exponentPowerOperators (bits : Nat) : Fin bits →
    UnitaryOperator (Recycling.Carrier.units modulus.toNat) :=
  fun position => unitTranslation modulus (unit ^ (2 ^ position.rev.val))

private def suffixPowerOperators (remaining position : Nat)
    (bounded : position + remaining ≤ bits) :
    Fin remaining → UnitaryOperator (Recycling.Carrier.units modulus.toNat) :=
  fun index => unitTranslation modulus
    (unit ^ (2 ^ (⟨position + index.val, by have bound := index.isLt; omega⟩ : Fin bits).rev.val))

private def suffixFeedbackPhases (inverse : Bool) (record : Fin bits → Fin 2)
    (remaining position : Nat) (bounded : position + remaining ≤ bits) : Fin remaining → ℂ :=
  fun index => recordFeedbackScalar inverse record
    ⟨position + index.val, by have bound := index.isLt; omega⟩ position
    (by change position ≤ position + index.val; omega)

private lemma suffixPowerOperators_next (remaining position : Nat)
    (bounded : position + (remaining + 1) ≤ bits) :
    (fun index => (suffixPowerOperators modulus unit (bits := bits) remaining (position + 1)
      (by omega) index :
      HilbertOperator (Recycling.Carrier.units modulus.toNat))) =
      fun index : Fin remaining =>
        (suffixPowerOperators modulus unit (bits := bits) (remaining + 1) position bounded
          index.succ :
          HilbertOperator (Recycling.Carrier.units modulus.toNat)) := by
  funext index
  have address : (⟨position + 1 + index.val, by have bound := index.isLt; omega⟩ : Fin bits) =
      ⟨position + index.succ.val, by have bound := index.isLt; omega⟩ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  exact congrArg (fun current : Fin bits =>
    (unitTranslation modulus (unit ^ (2 ^ current.rev.val)) :
      HilbertOperator (Recycling.Carrier.units modulus.toNat))) address

private lemma suffixFeedbackPhases_next (inverse : Bool) (record : Fin bits → Fin 2)
    (remaining position : Nat) (bounded : position + (remaining + 1) ≤ bits) :
    suffixFeedbackPhases inverse record remaining (position + 1) (by omega) =
      Partner.updatedPhases inverse remaining
        (suffixFeedbackPhases inverse record (remaining + 1) position bounded)
        (record ⟨position, by omega⟩) := by
  funext index
  let current : Fin bits := ⟨position + 1 + index.val, by have bound := index.isLt; omega⟩
  have address : (⟨position + index.succ.val, by have bound := index.isLt; omega⟩ : Fin bits) =
      current := by
    apply Fin.ext
    simp only [current, Fin.val_succ]
    omega
  change recordFeedbackScalar inverse record current (position + 1)
      (by change position + 1 ≤ position + 1 + index.val; omega) =
    recordFeedbackScalar inverse record
      (⟨position + index.succ.val, by have bound := index.isLt; omega⟩ : Fin bits) position
      (by change position ≤ position + index.succ.val; omega) *
        Partner.feedbackPhases inverse remaining (record ⟨position, by omega⟩) index
  have boundedAddress :
      (⟨(⟨position + index.succ.val, by have bound := index.isLt; omega⟩ : Fin bits),
        by change position ≤ position + index.succ.val; omega⟩ :
          {current : Fin bits // position ≤ current.val}) =
        ⟨current, by change position ≤ position + 1 + index.val; omega⟩ := Subtype.ext address
  have prior := congrArg
    (fun indexed : {current : Fin bits // position ≤ current.val} =>
      recordFeedbackScalar inverse record indexed.val position indexed.property) boundedAddress
  rw [prior, recordFeedbackScalar]
  have separation : current.val - position - 1 = index.val := by
    simp only [current]
    omega
  rw [separation, selectedScalar_rotation]
  exact mul_comm _ _

/-- Every suffix is the same shared Fourier contraction with its true measured-prefix phases. -/
lemma canonicalExponentSource_partner (inverse : Bool) (Reference : Register)
    (record : Fin bits → Fin 2) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) :
    canonicalExponentSource modulus unit inverse Reference record remaining position bounded =
      sourceWithReference
        (Partner.recycledKraus inverse remaining
          (fun index => (suffixPowerOperators modulus unit (bits := bits) remaining position bounded
            index :
            HilbertOperator (Recycling.Carrier.units modulus.toNat)))
          (suffixFeedbackPhases inverse record remaining position bounded)
          (readoutTail record remaining position bounded)) Reference := by
  induction remaining generalizing position with
  | zero =>
      simp only [canonicalExponentSource, Partner.recycledKraus, sourceWithReference_one]
  | succ remaining induction =>
      change canonicalExponentSource modulus unit inverse Reference record remaining (position + 1)
          (by omega) * canonicalStageSource modulus unit inverse Reference record
            ⟨position, by omega⟩ =
        sourceWithReference
          (Partner.recycledKraus inverse remaining
              (fun index => (suffixPowerOperators modulus unit (bits := bits) (remaining + 1)
                position bounded index.succ :
                  HilbertOperator (Recycling.Carrier.units modulus.toNat)))
              (Partner.updatedPhases inverse remaining
                (suffixFeedbackPhases inverse record (remaining + 1) position bounded)
                (record ⟨position, by omega⟩))
              (readoutTail record remaining (position + 1) (by omega)) *
            Partner.halfSum
              (suffixPowerOperators modulus unit (bits := bits) (remaining + 1) position bounded 0 :
                HilbertOperator (Recycling.Carrier.units modulus.toNat))
              (suffixFeedbackPhases inverse record (remaining + 1) position bounded 0)
              (record ⟨position, by omega⟩)) Reference
      rw [fourier_reference_product]
      apply congrArg₂ (fun left right :
        HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) => left * right)
      · refine (induction (position + 1) (by omega)).trans ?_
        exact congrArg (fun operator => sourceWithReference operator Reference)
          (congrArg₂
            (fun operators phases => Partner.recycledKraus inverse remaining operators phases
              (readoutTail record remaining (position + 1) (by omega)))
            (suffixPowerOperators_next modulus unit (bits := bits) remaining position bounded)
            (suffixFeedbackPhases_next inverse record remaining position bounded))
      · rfl

/-- Complete original exponent products are the shared source Kraus on the same partner. -/
lemma canonicalExponentSource_recycled (inverse : Bool) (Reference : Register)
    (outcome : Bits bits) :
    canonicalExponentSource modulus unit inverse Reference (tupleCoordinates bits outcome) bits
        0 (by omega) =
      sourceWithReference
        (Partner.recycledKraus inverse bits
          (fun index => (exponentPowerOperators modulus unit bits index :
            HilbertOperator (Recycling.Carrier.units modulus.toNat))) (fun _ => 1) outcome)
        Reference := by
  have whole := canonicalExponentSource_partner modulus unit inverse Reference
    (tupleCoordinates bits outcome) bits 0 (by omega)
  rw [readoutTail_all] at whole
  refine whole.trans ?_
  apply congrArg (fun operator => sourceWithReference operator Reference)
  apply congrArg₂ (fun operators phases =>
    Partner.recycledKraus inverse bits operators phases outcome)
  · funext index
    have address : (⟨0 + index.val, by have bound := index.isLt; omega⟩ : Fin bits) = index :=
      Fin.ext (by simp)
    change (unitTranslation modulus
      (unit ^ (2 ^ (⟨0 + index.val, by have bound := index.isLt; omega⟩ : Fin bits).rev.val)) :
        HilbertOperator (Recycling.Carrier.units modulus.toNat)) = _
    rw [address]
    rfl
  · rfl

/-- Canonical complete Fourier frequencies select precisely the same coherent exponent source. -/
lemma canonicalExponentSource_fullFourier (inverse : Bool) (Reference : Register)
    (frequency : Fin (2 ^ bits)) :
    canonicalExponentSource modulus unit inverse Reference
        (tupleCoordinates bits (frequencyBits bits frequency)) bits 0 (by omega) =
      sourceWithReference
        (Partner.fullOldKraus inverse bits
          (fun index => (exponentPowerOperators modulus unit bits index :
            HilbertOperator (Recycling.Carrier.units modulus.toNat))) frequency) Reference := by
  rw [canonicalExponentSource_recycled,
    ← Partner.qftPartner_oldKraus_eq_recycled inverse bits
      (exponentPowerOperators modulus unit bits),
    ← Partner.qftPartner_fullOldKraus_physical]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
