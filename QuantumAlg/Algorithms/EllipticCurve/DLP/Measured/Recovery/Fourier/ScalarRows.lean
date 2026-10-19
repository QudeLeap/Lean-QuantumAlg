/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Scalar Fourier rows in chronological physical coordinates

The only commutative products here are complex scalars. No arithmetic matrix, quantum
exponent, measured history or Store is commuted or converted to classical data. The
physical output order and its existing frequency reversal remain explicit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FourierScalar

noncomputable section

open QuantumAlg QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Earlier physical outcomes select the literal signed phase at this wire. -/
def before (inverse : Bool) {n : Nat} (output : Bits n) (current : Fin n) : ℂ :=
  ∏ previous : Fin n,
    if previous.val < current.val ∧ tupleCoordinates n output previous = 1 then
      Partner.rotation inverse (current.val - previous.val - 1)
    else 1

private lemma before_head (inverse : Bool) (n : Nat)
    (head : Fin 2) (tail : Bits n) :
    before inverse (n := n + 1) (head, tail) (0 : Fin (n + 1)) = 1 := by
  simp [before]

private lemma before_tail (inverse : Bool) (n : Nat)
    (head : Fin 2) (tail : Bits n) (current : Fin n) :
    before inverse (n := n + 1) (head, tail) current.succ =
      (if head = 1 then Partner.rotation inverse current.val else 1) *
        before inverse tail current := by
  unfold before
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, tupleCoordinates_head,
    tupleCoordinates_tail, Nat.zero_lt_succ, true_and, Nat.sub_zero,
    Nat.add_sub_cancel_right]
  apply congrArg (fun value : ℂ =>
    (if head = 1 then Partner.rotation inverse current.val else 1) * value)
  apply Finset.prod_congr rfl
  intro previous _
  have distance : current.val + 1 - (previous.val + 1) - 1 =
      current.val - previous.val - 1 := by omega
  simp only [Nat.add_lt_add_iff_right, distance]

/-- The product of actual H rows and earlier selected phases for one bit word. -/
def row (inverse : Bool) (n : Nat) (output input : Bits n) : ℂ :=
  ∏ current : Fin n,
    Gate.HOp (tupleCoordinates n output current) (tupleCoordinates n input current) *
      (if tupleCoordinates n input current = 0 then 1 else before inverse output current)

private lemma row_succ (inverse : Bool) (n : Nat) (head bit : Fin 2)
    (output input : Bits n) :
    row inverse (n + 1) (head, output) (bit, input) =
      row inverse n output input *
        Partner.phaseBasis n (Partner.feedbackPhases inverse n head) input * Gate.HOp head bit := by
  let hadamard : Fin 2 → Fin 2 → ℂ := fun left right => Gate.HOp left right
  change (∏ current : Fin (n + 1),
    hadamard (tupleCoordinates (n + 1) (head, output) current)
      (tupleCoordinates (n + 1) (bit, input) current) *
        (if tupleCoordinates (n + 1) (bit, input) current = 0 then 1 else
          before inverse (n := n + 1) (head, output) current)) =
      (∏ current : Fin n,
        hadamard (tupleCoordinates n output current) (tupleCoordinates n input current) *
          (if tupleCoordinates n input current = 0 then 1 else before inverse output current)) *
        Partner.phaseBasis n (Partner.feedbackPhases inverse n head) input * hadamard head bit
  rw [Fin.prod_univ_succ]
  simp (config := { zetaDelta := false }) only
    [tupleCoordinates_head, tupleCoordinates_tail, before_head, ite_self, mul_one]
  simp (config := { zetaDelta := false }) only [before_tail]
  have factor (index : Fin n) :
      hadamard (tupleCoordinates n output index) (tupleCoordinates n input index) *
        (if tupleCoordinates n input index = 0 then 1 else
          (if head = 1 then Partner.rotation inverse index.val else 1) *
            before inverse output index) =
      (hadamard (tupleCoordinates n output index) (tupleCoordinates n input index) *
        (if tupleCoordinates n input index = 0 then 1 else before inverse output index)) *
        (if tupleCoordinates n input index = 0 then 1 else
          (if head = 1 then Partner.rotation inverse index.val else 1)) := by
    by_cases zero : tupleCoordinates n input index = 0 <;>
      simp (config := { zetaDelta := false }) only [zero, ↓reduceIte] <;> ring
  simp (config := { zetaDelta := false }) only [factor]
  rw [Finset.prod_mul_distrib]
  simp (config := { zetaDelta := false }) only [Partner.phaseBasis, Partner.feedbackPhases]
  ring

/-- The scalar product is the existing signed no-SWAP Fourier row, with exact phase. -/
lemma row_eq_fourier (inverse : Bool) :
    ∀ (n : Nat) (output input : Bits n),
      row inverse n output input = Partner.fourierRows inverse n output input := by
  intro n
  induction n with
  | zero =>
      intro output input
      cases output
      cases input
      simp [row, Partner.fourierRows, coherent]
  | succ n ih =>
      intro output input
      rcases output with ⟨head, tail⟩
      rcases input with ⟨bit, rest⟩
      rw [row_succ, ih, Partner.fourierRows_succ]

/-- Negative feedback gives the inverse Fourier row at the reversed physical label. -/
lemma row_negative_frequency (n : Nat) (output input : Bits n) :
    row true n output input =
      ((QFTOperator n)⁻¹ : UnitaryOperator (Qubits n))
        (qftReverseBits n (binaryEquiv n output)) (binaryEquiv n input) := by
  rw [row_eq_fourier, Partner.qftPartner_fourierRows_entry]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FourierScalar
