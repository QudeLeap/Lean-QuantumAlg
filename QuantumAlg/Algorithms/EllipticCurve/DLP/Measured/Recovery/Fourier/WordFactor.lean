/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.BlockRows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Util.FinPow.BitReverse
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Extract Fourier scalars from the actual ordered measured arithmetic word

Point bank matrices retain both control values, including their literal arithmetic
resets and all exceptional/dirty-bank entries. Only scalar coefficients move. Different
measured Store paths remain separate and must later be summed as CP sandwiches.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FourierWord

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open scoped BigOperators

variable {B : Type} [Fintype B] [DecidableEq B]

/-- Chronological word on the original big-endian physical input tuple. -/
def tupleWord (n : Nat) (action : Nat → Bool → Matrix B B ℂ) (input : Bits n) : Matrix B B ℂ :=
  Partner.chronologicalProduct (List.ofFn (fun current : Fin n =>
    action current.rev.val (finTwoEquiv (tupleCoordinates n input current))))

private lemma tupleWord_succ (n : Nat) (action : Nat → Bool → Matrix B B ℂ)
    (head : Fin 2) (tail : Bits n) :
    tupleWord (n + 1) action (head, tail) =
      tupleWord n action tail * action n (finTwoEquiv head) := by
  unfold tupleWord
  rw [List.ofFn_succ, Partner.chronologicalProduct]
  simp only [tupleCoordinates_head, tupleCoordinates_tail]
  have headIndex : (0 : Fin (n + 1)).rev.val = n := by
    simp only [Fin.val_rev, Fin.val_zero]
    omega
  have tailIndex (index : Fin n) : index.succ.rev.val = index.rev.val := by
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  simp only [headIndex, tailIndex]

private lemma binary_head (n : Nat) (head : Fin 2) (tail : Bits n) :
    decide (2 ^ n ≤ (binaryEquiv (n + 1) (head, tail)).val) = finTwoEquiv head := by
  change decide (2 ^ n ≤ (qftPairEquiv n (head, binaryEquiv n tail)).val) = _
  rw [qftPairEquiv_apply_val]
  have bound := (binaryEquiv n tail).isLt
  fin_cases head
  · change decide (2 ^ n ≤ (binaryEquiv n tail).val + 2 ^ n * 0) = false
    rw [mul_zero, Nat.add_zero]
    exact decide_eq_false (Nat.not_le_of_gt bound)
  · change decide (2 ^ n ≤ (binaryEquiv n tail).val + 2 ^ n * 1) = true
    rw [mul_one]
    exact decide_eq_true (Nat.le_add_left _ _)

private lemma binary_tail (n : Nat) (head : Fin 2) (tail : Bits n) :
    (binaryEquiv (n + 1) (head, tail)).val % 2 ^ n = (binaryEquiv n tail).val :=
  qftPairEquiv_mod_tail n head (binaryEquiv n tail)

/-- The integer MSB recursion is the same original ordered physical word. -/
lemma word_eq_tupleWord (action : Nat → Bool → Matrix B B ℂ) :
    ∀ (n : Nat) (input : Bits n),
      OrderedBankWord.word action n (binaryEquiv n input).val =
        tupleWord n action input := by
  intro n
  induction n with
  | zero => intro input; simp [OrderedBankWord.word, tupleWord, Partner.chronologicalProduct]
  | succ n ih =>
      intro input
      rcases input with ⟨head, tail⟩
      change OrderedBankWord.word action n ((binaryEquiv (n + 1)
        (head, tail)).val % 2 ^ n) *
        action n (decide (2 ^ n ≤ (binaryEquiv (n + 1) (head, tail)).val)) = _
      rw [binary_tail, binary_head, ih, tupleWord_succ]

private lemma chronological_smul {A : Type} (items : List A)
    (coefficients : A → ℂ) (matrices : A → Matrix B B ℂ) :
    Partner.chronologicalProduct (items.map (fun item => coefficients item • matrices item)) =
      (items.map coefficients).prod • Partner.chronologicalProduct (items.map matrices) := by
  induction items with
  | nil => simp [Partner.chronologicalProduct]
  | cons item tail ih =>
      simp only [List.map_cons, List.prod_cons, Partner.chronologicalProduct, ih,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]

/-- Extract scalars while retaining every arithmetic matrix in chronological order. -/
lemma tupleWord_smul (n : Nat) (input : Bits n)
    (coefficients : Nat → Bool → ℂ) (matrices : Nat → Bool → Matrix B B ℂ) :
    tupleWord n (fun remaining bit => coefficients remaining bit • matrices remaining bit) input =
      (∏ current : Fin n,
        coefficients current.rev.val (finTwoEquiv (tupleCoordinates n input current))) •
          tupleWord n matrices input := by
  have actual := chronological_smul (List.ofFn (fun current : Fin n => current))
    (fun current => coefficients current.rev.val (finTwoEquiv (tupleCoordinates n input current)))
    (fun current => matrices current.rev.val (finTwoEquiv (tupleCoordinates n input current)))
  simpa only [tupleWord, List.map_ofFn, Function.comp_def, List.prod_ofFn] using actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FourierWord

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity
namespace ActualFeedback

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open Recovery.Stage.PointCoordinates
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma bitBasis_finTwo (bit : Fin 2) : bitBasis (finTwoEquiv bit) = bit := by
  fin_cases bit <;> rfl

/-- The actual all-label arithmetic factor, with the Fourier scalar removed only. -/
def pathBankAction {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m) (second : Bool) :
    Nat → Bool → Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  fun remaining emitted => if bounded : remaining < m then
    let index := blockIndex second ⟨remaining, bounded⟩
    bankBlock (environment := environment) E (points index) m Reference (path index).2.2 (path
      index).1 (bitBasis emitted)
  else 1

private def pathCoefficient (width m : Nat)
    (path : Fin (2 * m) → Branch width m) (second : Bool) : Nat → Bool → ℂ :=
  fun remaining emitted => if bounded : remaining < m then
    let index := blockIndex second ⟨remaining, bounded⟩
    Gate.HOp (ReadoutRows.outcomeBit width m (path index).2.1) (bitBasis emitted) *
      FeedbackRows.feedbackPhase width m index (path index).1 (bitBasis emitted)
        (Recovery.Layout.order m)
  else 1

private lemma blockAction_factor {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m) (second : Bool) :
    blockAction (environment := environment) E points Reference second
      (fun index => (path index).2.2)
      (fun index => (path index).1) (fun index => (path index).2.1) =
      fun remaining emitted => pathCoefficient p.size m path second remaining emitted •
        pathBankAction (environment := environment) E points Reference path second remaining
          emitted := by
  funext remaining emitted
  by_cases bounded : remaining < m
  · simp only [blockAction, pathCoefficient, pathBankAction, dif_pos bounded, action]
  · simp only [blockAction, pathCoefficient, pathBankAction, dif_neg bounded, one_smul]

/-- Each legal actual branch has its negative Fourier row multiplying the original bank word. -/
lemma actual_word_fourier {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (original final : Store (Recovery.Layout.terminal p.size m))
    (valid : traceValid p.size m (2 * m) id path original final)
    (second : Bool) (input : Bits m) :
    OrderedBankWord.word
        (blockAction (environment := environment) E points Reference second
          (fun index => (path index).2.2)
          (fun index => (path index).1) (fun index => (path index).2.1))
        m (binaryEquiv m input).val =
      Partner.fourierRows true m (blockOutput p.size m path second) input •
        OrderedBankWord.word (pathBankAction (environment :=
          environment) E points Reference path second)
          m (binaryEquiv m input).val := by
  rw [blockAction_factor, FourierWord.word_eq_tupleWord, FourierWord.tupleWord_smul,
    ← FourierWord.word_eq_tupleWord]
  have coefficients :
      (∏ current : Fin m,
        pathCoefficient p.size m path second current.rev.val
          (finTwoEquiv (tupleCoordinates m input current))) =
      Partner.fourierRows true m (blockOutput p.size m path second) input := by
    rw [← actual_block_row p.size m path original final valid second input]
    apply Finset.prod_congr rfl
    intro current _
    simp only [pathCoefficient, dif_pos current.rev.isLt, position, bitBasis_finTwo]
  rw [coefficients]

end

end ActualFeedback
end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
