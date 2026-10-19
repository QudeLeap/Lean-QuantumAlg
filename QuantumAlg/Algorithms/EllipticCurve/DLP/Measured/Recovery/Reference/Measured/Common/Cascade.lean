/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Kernel
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Stored.Cascade
import Mathlib.Data.Matrix.Block

/-!
# The actual old cascade's off-diagonal recurrence on one fixed quantum bank

The same real arithmetic Store path acts on both exponent blocks. Branches are summed
only after the matrix sandwich. The word is tail times head, preserving every original
point factor. This owner does not prove old preparation, Fourier, conversions, DLP
framing, terminal measurements, old/new Store-history reconstruction or common sigma.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Measured.CommonBank

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The original ordered word acts on one fixed bank, indexed coherently by all exponents. -/
def bankWord
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register) :
    (length : Nat) → (Fin length → Fin count) → (Fin length → Branch p.size count) →
      Exponents count → Matrix (Bank p.size Reference) (Bank p.size Reference) ℂ
  | 0, _, _, _ => 1
  | length + 1, indices, path, exponent =>
      bankWord (environment := environment) E points Reference length (Fin.tail indices) (Fin.tail
        path) exponent *
        bankKraus (environment := environment) E (points (indices 0)) (indices 0) Reference (path
          0).2 (path 0).1
          (exponent (indices 0))

/-- The actual full-register chronological kernel has exactly these fixed-bank blocks. -/
lemma traceKraus_bankFirst {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin count) (path : Fin length → Branch p.size count) :
    (traceKraus (environment := environment) E points Reference length indices path).submatrix
        (bankFirst p.size count Reference).symm (bankFirst p.size count Reference).symm =
      Matrix.blockDiagonal (bankWord (environment := environment) E points Reference length
        indices path) := by
  induction length with
  | zero =>
      simp only [traceKraus, bankWord, Matrix.submatrix_one_equiv]
      change (1 : Matrix (Bank p.size Reference × Exponents count)
        (Bank p.size Reference × Exponents count) ℂ) =
          Matrix.blockDiagonal (1 : Exponents count →
            Matrix (Bank p.size Reference) (Bank p.size Reference) ℂ)
      exact Matrix.blockDiagonal_one.symm
  | succ length ih =>
      let basis := bankFirst p.size count Reference
      let tail := traceKraus (environment := environment) E points Reference length (Fin.tail
        indices) (Fin.tail path)
      let head := stepKraus (environment := environment) E (points (indices 0)) (indices 0)
        Reference (path 0).2 (path 0).1
      change (tail * head).submatrix basis.symm basis.symm = _
      calc
        _ = tail.submatrix basis.symm basis.symm *
            head.submatrix basis.symm basis.symm :=
          (Matrix.submatrix_mul_equiv tail head basis.symm basis.symm basis.symm).symm
        _ = Matrix.blockDiagonal
              (bankWord (environment := environment) E points Reference length (Fin.tail indices)
                (Fin.tail path)) *
            Matrix.blockDiagonal (fun exponent : Exponents count =>
              bankKraus (environment := environment) E (points (indices 0)) (indices 0) Reference
                (path 0).2 (path 0).1
                (exponent (indices 0))) := by
          rw [ih, stepKraus_bankFirst]
        _ = Matrix.blockDiagonal (fun exponent : Exponents count =>
            bankWord (environment := environment) E points Reference length (Fin.tail indices)
              (Fin.tail path) exponent *
              bankKraus (environment := environment) E (points (indices 0)) (indices 0) Reference
                (path 0).2 (path 0).1
                (exponent (indices 0))) := (Matrix.blockDiagonal_mul _ _).symm
        _ = _ := rfl

/-- One actual original path evolves an arbitrary u/u' input block as W(u) X W(u')*. -/
lemma trace_sandwich_offdiagonal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin count) (path : Fin length → Branch p.size count)
    (density : Matrix ((readyContext p.size count).register.prod Reference).Index
      ((readyContext p.size count).register.prod Reference).Index ℂ)
    (left right : Exponents count) :
    (traceKraus (environment := environment) E points Reference length indices path * density *
      (traceKraus (environment := environment) E points Reference length indices
        path).conjTranspose).submatrix
        (fun bank => (coordinates p.size count Reference).symm (left, bank))
        (fun bank => (coordinates p.size count Reference).symm (right, bank)) =
      bankWord (environment := environment) E points Reference length indices path left *
        density.submatrix
        (fun bank => (coordinates p.size count Reference).symm (left, bank))
        (fun bank => (coordinates p.size count Reference).symm (right, bank)) *
          (bankWord (environment := environment) E points Reference length indices path
            right).conjTranspose :=
  physical_sandwich_offdiagonal Reference _ _
    (traceKraus_bankFirst E points Reference length indices path) density left right

/-- Actual original prefix execution retains all off-diagonal exponent/reference blocks. -/
lemma actual_cascade_store_offdiagonal {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin count) {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (readyContext p.size count)) (left right : Exponents count) :
    (storeDensity ((cascade E points (List.ofFn indices)).execute environment Reference state)
      final).submatrix
        (fun bank => (coordinates p.size count Reference).symm (left, bank))
        (fun bank => (coordinates p.size count Reference).symm (right, bank)) =
      ∑ path : Fin length → Branch p.size count,
        ∑ original : Store (readyContext p.size count),
          if traceValid p.size length indices path original final then
            bankWord (environment := environment) E points Reference length indices path left *
              (storeDensity state original).submatrix
                (fun bank => (coordinates p.size count Reference).symm (left, bank))
                (fun bank => (coordinates p.size count Reference).symm (right, bank)) *
              (bankWord (environment := environment) E points Reference length indices path
                right).conjTranspose
          else 0 := by
  rw [actual_cascade_store_density]
  unfold traceDensity
  ext row column
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro path _
  apply Finset.sum_congr rfl
  intro original _
  by_cases legal : traceValid p.size length indices path original final
  · rw [if_pos legal, if_pos legal]
    exact congrArg (fun matrix => matrix row column)
      (trace_sandwich_offdiagonal E points Reference length indices path
        (storeDensity state original) left right)
  · simp only [if_neg legal, Matrix.zero_apply]

/-- Every indexed call in the original increasing-index cascade uses this same fixed bank. -/
lemma actual_fullCascade_store_offdiagonal {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (readyContext p.size count)) (left right : Exponents count) :
    (storeDensity ((fullCascade E points).execute environment Reference state) final).submatrix
        (fun bank => (coordinates p.size count Reference).symm (left, bank))
        (fun bank => (coordinates p.size count Reference).symm (right, bank)) =
      ∑ path : Fin count → Branch p.size count,
        ∑ original : Store (readyContext p.size count),
          if traceValid p.size count id path original final then
            bankWord (environment := environment) E points Reference count id path left *
              (storeDensity state original).submatrix
                (fun bank => (coordinates p.size count Reference).symm (left, bank))
                (fun bank => (coordinates p.size count Reference).symm (right, bank)) *
              (bankWord (environment := environment) E points Reference count id path
                right).conjTranspose
          else 0 := by
  have actual := actual_cascade_store_offdiagonal (environment := environment) E points Reference
    count id
    state final left right
  change (storeDensity ((fullCascade E points).execute environment Reference state) final).submatrix
    (fun bank => (coordinates p.size count Reference).symm (left, bank))
    (fun bank => (coordinates p.size count Reference).symm (right, bank)) = _ at actual
  exact actual

end

end Measured.CommonBank
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
