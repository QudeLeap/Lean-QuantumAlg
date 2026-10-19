/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Core.Measure.Kraus
import Mathlib.Tactic.Ext

/-!
# Recursive coherent and adaptive Fourier instruments

The physical recursion applies a leading one-qubit gate, diagonal feedback on
the remaining wires, and the tail transform. Measuring the leading wire before
feedback preserves the exact joint instrument, including every measured wire
and every untouched reference system.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

open QuantumAlg.MeasurementInstrument

noncomputable section

/-- The tuple follows the physical leading-wire order, before output reversal. -/
@[expose] public def Bits : Nat → Type
  | 0 => Unit
  | n + 1 => Fin 2 × Bits n

public instance bitsFintype : (n : Nat) → Fintype (Bits n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
      letI := bitsFintype n
      exact inferInstanceAs (Fintype (Fin 2 × Bits n))

public instance bitsDecidableEq : (n : Nat) → DecidableEq (Bits n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => by
      letI := bitsDecidableEq n
      exact inferInstanceAs (DecidableEq (Fin 2 × Bits n))

/-- Actual products for every coherent stage; the zero-wire circuit is identity. -/
public def coherent (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex) :
    (n : Nat) → Matrix (Bits n) (Bits n) Complex
  | 0 => fun _ _ => 1
  | n + 1 => coherentStage H (U n) (coherent H U n)

/-- Actual adaptive composition: leading gate and measurement, feedback, recursion. -/
public def adaptiveKraus (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex) :
    (n : Nat) → Bits n → Matrix Unit (Bits n) Complex
  | 0, _ => fun _ _ => 1
  | n + 1, y => adaptiveKraus H U n y.2 * U n y.1 * headKraus H y.1

/-- Arbitrary-size exact Kraus equality, including the phase of each branch. -/
public lemma adaptiveKraus_eq_coherent_row
    (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex) :
    ∀ (n : Nat) (y : Bits n), adaptiveKraus H U n y = rowKraus (coherent H U n) y := by
  intro n
  induction n with
  | zero =>
      intro y
      ext u x
      cases y
      cases u
      cases x
      simp [adaptiveKraus, coherent, rowKraus]
  | succ n ih =>
      intro y
      rcases y with ⟨b, tail⟩
      change adaptiveKraus H U n tail * U n b * headKraus H b =
        rowKraus (coherentStage H (U n) (coherent H U n)) (b, tail)
      rw [ih, rowKraus_stage]

/-- Full classical-quantum state equality for arbitrary input operators and references. -/
public lemma adaptive_cqInstrument_eq_coherent
    (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex)
    (n : Nat) {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) :
    cqInstrument (adaptiveKraus H U n) ρ =
      cqInstrument (fun y => rowKraus (coherent H U n) y) ρ := by
  have rows : adaptiveKraus H U n = fun y => rowKraus (coherent H U n) y := by
    funext y
    exact adaptiveKraus_eq_coherent_row H U n y
  rw [rows]

/-- The empty transform has one outcome and preserves the complete reference state. -/
public lemma zero_referenceBranch
    (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex)
    {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits 0 × R) (Bits 0 × R) Complex) (r s : R) :
    referenceBranch (adaptiveKraus H U 0 ()) ρ r s = ρ ((), r) ((), s) := by
  change referenceBranch (fun _ : Unit => fun _ : Unit => (1 : Complex)) ρ r s = _
  simp only [referenceBranch, Matrix.mul_apply, Matrix.conjTranspose_apply, withReference,
    mul_ite, mul_one, mul_zero, Complex.star_def, MonoidWithZeroHom.map_ite_one_zero,
    Fintype.sum_prod_type, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_singleton]
  change (∑ x : Unit × R, (1 * (if r = x.2 then (1 : Complex) else 0)) *
    ρ x ((), s)) = _
  simp [Fintype.sum_prod_type, ite_mul]
  rfl

/-- Complete instrument equality retains the actual physical output bits, without a SWAP. -/
public lemma adaptive_retainedInstrument_eq_coherent
    (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex)
    (n : Nat) {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) :
    retainedInstrument (fun y : Bits n => y) (adaptiveKraus H U n) ρ =
      retainedInstrument (fun y : Bits n => y)
        (fun y => rowKraus (coherent H U n) y) ρ := by
  have rows : adaptiveKraus H U n = fun y => rowKraus (coherent H U n) y := by
    funext y
    exact adaptiveKraus_eq_coherent_row H U n y
  rw [rows]

/-- The same branch state can be embedded in any reset space.
No unequal-space identity is asserted. -/
public lemma adaptive_resetBank_factor
    (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex)
    (n : Nat) (y : Bits n) {B R : Type} [DecidableEq B]
    [Fintype R] [DecidableEq R] (reset : B)
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) :
    bankBranch reset (adaptiveKraus H U n y) ρ =
      bankEmbedding reset * referenceBranch (rowKraus (coherent H U n) y) ρ *
        (bankEmbedding reset).conjTranspose := by
  rw [adaptiveKraus_eq_coherent_row, bankBranch_factor]

/-- The same physical recursion with conjugated gates gives the conjugate full matrix. -/
public lemma coherent_conjugate
    (H : Matrix (Fin 2) (Fin 2) Complex)
    (U : (n : Nat) → Fin 2 → Matrix (Bits n) (Bits n) Complex) (n : Nat) :
    coherent (conjugate H) (fun m b => conjugate (U m b)) n =
      conjugate (coherent H U n) := by
  induction n with
  | zero =>
      ext i j
      simp [coherent, conjugate]
  | succ n ih =>
      change coherentStage (conjugate H) (fun b => conjugate (U n b))
          (coherent (conjugate H) (fun m b => conjugate (U m b)) n) =
        conjugate (coherentStage H (U n) (coherent H U n))
      rw [ih]
      unfold coherentStage
      rw [conjugate_mul, conjugate_mul, conjugate_controlled, conjugate_controlled,
        conjugate_leading]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
