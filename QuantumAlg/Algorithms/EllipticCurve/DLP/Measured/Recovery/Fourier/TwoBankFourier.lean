/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.WordFactor
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Initialized.Execution
import Mathlib.Algebra.BigOperators.Fin

/-!
# Two exact interval amplitudes and Fourier rows on the actual measured bank word

 Exponent labels
are coherent within one measured path. Distinct paths and complete original
Store fibers are summed only as CP sandwiches. No arithmetic matrices commute.
The physical allocator, old-protocol path correspondence and conversion boundary
remain separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord
namespace InitializedPaths

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open StoredRecursion PathDensity PathDensity.ActualFeedback
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma sum_range_binary {A : Type} [AddCommMonoid A] (m : Nat) (f : Nat → A) :
    (∑ value ∈ Finset.range (2 ^ m), f value) =
      ∑ input : Bits m, f (binaryEquiv m input).val := by
  rw [Finset.sum_range]
  exact ((binaryEquiv m).sum_comp (fun value : Fin (2 ^ m) => f value.val)).symm

/-- Physical two-exponent Fourier coefficient, with the actual arithmetic word in order. -/
def fourierBankWord {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  ∑ secondInput : Bits m, ∑ firstInput : Bits m,
    ((((if (binaryEquiv m secondInput).val < r then invSqrt r else 0 : ℝ) : ℂ) *
        ((if (binaryEquiv m firstInput).val < r then invSqrt r else 0 : ℝ) : ℂ)) *
      (Partner.fourierRows true m (blockOutput p.size m path true) secondInput *
        Partner.fourierRows true m (blockOutput p.size m path false) firstInput)) •
      OrderedBankWord.exponentPair
        (pathBankAction (environment := environment) E points Reference path false)
        (pathBankAction (environment := environment) E points Reference path true)
        m (binaryEquiv m firstInput).val (binaryEquiv m secondInput).val

/-- Only complex scalars move; the second arithmetic word still multiplies the first. -/
lemma actual_exponent_pair_fourier {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (original final : Store (Recovery.Layout.terminal p.size m))
    (valid : traceValid p.size m (2 * m) id path original final)
    (firstInput secondInput : Bits m) :
    OrderedBankWord.exponentPair
        (blockAction (environment := environment) E points Reference false
          (fun index => (path index).2.2)
          (fun index => (path index).1) (fun index => (path index).2.1))
        (blockAction (environment := environment) E points Reference true
          (fun index => (path index).2.2)
          (fun index => (path index).1) (fun index => (path index).2.1))
        m (binaryEquiv m firstInput).val (binaryEquiv m secondInput).val =
      (Partner.fourierRows true m (blockOutput p.size m path true) secondInput *
        Partner.fourierRows true m (blockOutput p.size m path false) firstInput) •
        OrderedBankWord.exponentPair
          (pathBankAction (environment := environment) E points Reference path false)
          (pathBankAction (environment := environment) E points Reference path true)
          m (binaryEquiv m firstInput).val (binaryEquiv m secondInput).val := by
  unfold OrderedBankWord.exponentPair
  rw [actual_word_fourier E points Reference path original final valid true secondInput,
    actual_word_fourier E points Reference path original final valid false firstInput,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- The actual initialized stream has exactly the two coherent Fourier-weighted words. -/
lemma bankWord_eq_fourierBankWord {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (original final : Store (Recovery.Layout.terminal p.size m))
    (valid : traceValid p.size m (2 * m) id path original final) :
    bankWord (environment := environment) E r points Reference path = fourierBankWord (environment
      := environment) E r points Reference path := by
  unfold bankWord fourierBankWord
  rw [sum_range_binary]
  apply Finset.sum_congr rfl
  intro secondInput _
  rw [sum_range_binary]
  apply Finset.sum_congr rfl
  intro firstInput _
  rw [actual_exponent_pair_fourier E points Reference path original final valid
    firstInput secondInput, smul_smul]

private lemma conditional_sandwich_sum_congr
    {Path Original Bank Output : Type} [Fintype Path] [Fintype Original] [Fintype Bank]
    (columns : Matrix Output Bank ℂ) (density : Original → Matrix Bank Bank ℂ)
    (before after : Path → Matrix Bank Bank ℂ) (valid : Path → Original → Prop)
    (same : ∀ path original, valid path original → before path = after path) :
    (∑ path, ∑ original, if valid path original then
      columns * (before path * density original * (before path).conjTranspose) *
        columns.conjTranspose else 0) =
    ∑ path, ∑ original, if valid path original then
      columns * (after path * density original * (after path).conjTranspose) *
        columns.conjTranspose else 0 := by
  apply Finset.sum_congr rfl
  intro path _
  apply Finset.sum_congr rfl
  intro original _
  by_cases legal : valid path original
  · rw [if_pos legal, if_pos legal, same path original legal]
  · rw [if_neg legal, if_neg legal]

/-- Each complete final Store retains every legal path with its original CP multiplicity. -/
lemma actual_initialized_fourier_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (density : Store (Recovery.Layout.terminal p.size m) →
      Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ)
    (initialized : ∀ original : Store (Recovery.Layout.terminal p.size m),
      storeDensity state original =
        initializedColumns p.size m Reference * density original *
          (initializedColumns p.size m Reference).conjTranspose)
    (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((stages E r points (Recovery.Layout.order m)).execute environment Reference
      state) final =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (fourierBankWord (environment := environment) E r points Reference path * density
                original *
                (fourierBankWord (environment := environment) E r points Reference
                  path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0 := by
  have actual := actual_initialized_store_density (environment := environment) E r points
    Reference state density initialized
    positive fits final
  exact actual.trans (conditional_sandwich_sum_congr
    (initializedColumns p.size m Reference) density
    (bankWord (environment := environment) E r points Reference) (fourierBankWord (environment :=
      environment) E r points Reference)
    (fun path original => traceValid p.size m (2 * m) id path original final)
    (fun path original legal =>
      bankWord_eq_fourierBankWord E r points Reference path original final legal))

end

end InitializedPaths
end PointCoordinates.StageWord.PathWord
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
