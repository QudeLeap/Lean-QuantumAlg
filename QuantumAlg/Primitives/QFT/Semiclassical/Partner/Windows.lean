/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Blocks

/-!
# Ordered symbolic windows of the same Fourier contraction

A structural list fold makes the existing exact two-block cut repeatedly.
Every suffix inherits the phases of the actual preceding outcome block;
operator factors keep their order. Widths, including zero, stay symbolic.
These are mathematical operators and labels, with no circuit, physical
source bank or claim about an arithmetic implementation.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

variable {S : Register}

/-- The addition order follows the canonical leading-block contraction cut. -/
def windowWidth : List Nat → Nat
  | [] => 0
  | head :: tail => windowWidth tail + head

/-- Original chronological outcome blocks, retaining every bit of every window. -/
def WindowBits : List Nat → Type
  | [] => Unit
  | head :: tail => Bits head × WindowBits tail

/-- Concatenate the same chronological outcomes using only the existing exact block map. -/
def windowBits : (widths : List Nat) → WindowBits widths → Bits (windowWidth widths)
  | [], _ => ()
  | head :: tail, output =>
      blockBits head (windowWidth tail) output.1 (windowBits tail output.2)

/-- Each original window acts before the suffix carrying its inherited measured feedback. -/
def windowContraction (inverse : Bool) : (widths : List Nat) →
    (Fin (windowWidth widths) → HilbertOperator S) →
    (Fin (windowWidth widths) → Complex) → WindowBits widths → HilbertOperator S
  | [], _, _, _ => 1
  | head :: tail, operators, phases, output =>
      windowContraction inverse tail (suffixFamily (windowWidth tail) head operators)
          (suffixPhases inverse head (windowWidth tail) phases output.1) output.2 *
        contraction inverse head (prefixFamily (windowWidth tail) head operators)
          (prefixFamily (windowWidth tail) head phases) output.1

/-- The structural width is exactly the original sum, without expanding the list. -/
lemma qftPartner_windowWidth_sum (widths : List Nat) : windowWidth widths = widths.sum := by
  induction widths with
  | nil => rfl
  | cons head tail ih => rw [windowWidth, ih, List.sum_cons, Nat.add_comm]

/-- Every ordered symbolic window fold is the same full source contraction. -/
lemma qftPartner_windowContraction (inverse : Bool) :
    ∀ (widths : List Nat) (operators : Fin (windowWidth widths) → HilbertOperator S)
      (phases : Fin (windowWidth widths) → Complex) (output : WindowBits widths),
      windowContraction inverse widths operators phases output =
        contraction inverse (windowWidth widths) operators phases (windowBits widths output) := by
  intro widths
  induction widths with
  | nil =>
      intro operators phases output
      rw [qftPartner_contraction_eq_recycled]
      rfl
  | cons head tail ih =>
      intro operators phases output
      change windowContraction inverse tail
          (suffixFamily (windowWidth tail) head operators)
          (suffixPhases inverse head (windowWidth tail) phases output.1) output.2 *
        contraction inverse head (prefixFamily (windowWidth tail) head operators)
          (prefixFamily (windowWidth tail) head phases) output.1 =
        contraction inverse (windowWidth tail + head) operators phases
          (blockBits head (windowWidth tail) output.1 (windowBits tail output.2))
      rw [ih]
      exact (qftPartner_contraction_blocks inverse head (windowWidth tail)
        operators phases output.1 (windowBits tail output.2)).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
