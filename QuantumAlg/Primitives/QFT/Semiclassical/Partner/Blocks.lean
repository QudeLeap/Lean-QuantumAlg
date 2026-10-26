/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics

/-!
# Exact symbolic cuts of the ordered recycled Fourier contraction

These are mathematical factorization laws for the existing source recurrence.
The suffix receives every phase actually accumulated from the measured prefix.
Partner operators keep their order and need not commute. No physical bank,
circuit, measurement or point translation is constructed by this module.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

variable {S : Register}

/-- Original leading labels; the addition order permits structural recursion on their count. -/
def prefixFamily {Value : Type} (tailCount headCount : Nat)
    (family : Fin (tailCount + headCount) → Value) : Fin headCount → Value :=
  fun index => family ⟨index.val, by have bound := index.isLt; omega⟩

/-- Original trailing labels remain after the measured leading positions. -/
def suffixFamily {Value : Type} (tailCount headCount : Nat)
    (family : Fin (tailCount + headCount) → Value) : Fin tailCount → Value :=
  fun index => family ⟨index.val + headCount, Nat.add_lt_add_right index.isLt headCount⟩

private lemma prefixFamily_head {Value : Type} (tailCount headCount : Nat)
    (family : Fin (tailCount + (headCount + 1)) → Value) :
    prefixFamily tailCount (headCount + 1) family 0 = family 0 := rfl

private lemma prefixFamily_tail {Value : Type} (tailCount headCount : Nat)
    (family : Fin (tailCount + (headCount + 1)) → Value) :
    prefixFamily tailCount headCount (fun index => family index.succ) =
      (fun index => prefixFamily tailCount (headCount + 1) family index.succ) := rfl

private lemma suffixFamily_succ {Value : Type} (tailCount headCount : Nat)
    (family : Fin (tailCount + (headCount + 1)) → Value) :
    suffixFamily tailCount headCount (fun index => family index.succ) =
      suffixFamily tailCount (headCount + 1) family := rfl

private lemma prefixFamily_updated (inverse : Bool) (tailCount headCount : Nat)
    (phases : Fin (tailCount + (headCount + 1)) → Complex) (head : Fin 2) :
    prefixFamily tailCount headCount
        (updatedPhases inverse (tailCount + headCount) phases head) =
      updatedPhases inverse headCount
        (prefixFamily tailCount (headCount + 1) phases) head := rfl

/-- The same physical chronological labels, without a frequency reversal or wire permutation. -/
def blockBits : (headCount tailCount : Nat) → Bits headCount → Bits tailCount →
    Bits (tailCount + headCount)
  | 0, _, _, tail => tail
  | headCount + 1, tailCount, front, tail =>
      (front.1, blockBits headCount tailCount front.2 tail)

/-- Real prefix outcomes update the still-unmeasured suffix phases one actual head at a time. -/
def suffixPhases (inverse : Bool) : (headCount tailCount : Nat) →
    (Fin (tailCount + headCount) → Complex) → Bits headCount → Fin tailCount → Complex
  | 0, _, phases, _ => phases
  | headCount + 1, tailCount, phases, output =>
      suffixPhases inverse headCount tailCount
        (updatedPhases inverse (tailCount + headCount) phases output.1) output.2

/-- An exact cut preserves the chronological operator product and all inherited feedback. -/
lemma qftPartner_recycledKraus_blocks (inverse : Bool) :
    ∀ (headCount tailCount : Nat)
      (operators : Fin (tailCount + headCount) → HilbertOperator S)
      (phases : Fin (tailCount + headCount) → Complex)
      (front : Bits headCount) (tail : Bits tailCount),
      recycledKraus inverse (tailCount + headCount) operators phases
          (blockBits headCount tailCount front tail) =
        recycledKraus inverse tailCount (suffixFamily tailCount headCount operators)
            (suffixPhases inverse headCount tailCount phases front) tail *
          recycledKraus inverse headCount (prefixFamily tailCount headCount operators)
            (prefixFamily tailCount headCount phases) front := by
  intro headCount
  induction headCount with
  | zero =>
      intro tailCount operators phases front tail
      have unchanged : suffixFamily tailCount 0 operators = operators := by
        funext index
        exact congrArg operators (Fin.ext (Nat.add_zero index.val))
      simp only [blockBits, suffixPhases, recycledKraus, Nat.add_zero, Matrix.mul_one,
        unchanged]
  | succ headCount ih =>
      intro tailCount operators phases front tail
      rcases front with ⟨head, front⟩
      change
        recycledKraus inverse (tailCount + headCount) (fun index => operators index.succ)
            (updatedPhases inverse (tailCount + headCount) phases head)
            (blockBits headCount tailCount front tail) *
          halfSum (operators 0) (phases 0) head =
        recycledKraus inverse tailCount (suffixFamily tailCount (headCount + 1) operators)
            (suffixPhases inverse headCount tailCount
              (updatedPhases inverse (tailCount + headCount) phases head) front) tail *
          (recycledKraus inverse headCount
              (fun index => prefixFamily tailCount (headCount + 1) operators index.succ)
              (updatedPhases inverse headCount
                (prefixFamily tailCount (headCount + 1) phases) head) front *
            halfSum (prefixFamily tailCount (headCount + 1) operators 0)
              (prefixFamily tailCount (headCount + 1) phases 0) head)
      rw [ih]
      simp only [suffixFamily_succ, prefixFamily_tail, prefixFamily_updated,
        prefixFamily_head, Matrix.mul_assoc]

/-- The independently defined Fourier source contraction has the same exact two-block cut. -/
lemma qftPartner_contraction_blocks (inverse : Bool) (headCount tailCount : Nat)
    (operators : Fin (tailCount + headCount) → HilbertOperator S)
    (phases : Fin (tailCount + headCount) → Complex)
    (front : Bits headCount) (tail : Bits tailCount) :
    contraction inverse (tailCount + headCount) operators phases
        (blockBits headCount tailCount front tail) =
      contraction inverse tailCount (suffixFamily tailCount headCount operators)
          (suffixPhases inverse headCount tailCount phases front) tail *
        contraction inverse headCount (prefixFamily tailCount headCount operators)
          (prefixFamily tailCount headCount phases) front := by
  rw [qftPartner_contraction_eq_recycled, qftPartner_recycledKraus_blocks,
    qftPartner_contraction_eq_recycled, qftPartner_contraction_eq_recycled]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
