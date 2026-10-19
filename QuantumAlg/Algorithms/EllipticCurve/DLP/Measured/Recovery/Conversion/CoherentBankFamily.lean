/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.OutputBankDensity

/-!
# Both coherent source indices in the literal converted bank family

Each actual measured path contains a coherent sum over the two source
exponents. Its CP sandwich therefore retains two independently varying
source pairs. Cross terms are kept before the outer sums over actual paths
and complete original Stores. All four conversions keep their actual order.

These identities concern arbitrary matrices, including every off-diagonal
Reference entry. They impose no normalization, positive mass, nonzero width,
clean input, admissible-branch or caller certificate. They establish no
good-component agreement, virtual-source channel contraction or success floor.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace CoherentBankFamily

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A coherent CP sandwich retains every pair of source labels and their relative phases. -/
lemma coherent_sandwich {Source Input Output : Type}
    [Fintype Source] [Fintype Input]
    (amplitude : Source → ℂ) (word : Source → Matrix Output Input ℂ)
    (density : Matrix Input Input ℂ) :
    (∑ source, amplitude source • word source) * density *
        (∑ source, amplitude source • word source).conjTranspose =
      ∑ left, ∑ right, (amplitude left * star (amplitude right)) •
        (word left * density * (word right).conjTranspose) := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

open QuantumAlg QuantumAlg.Execution
open _root_.QuantumAlg.MeasuredUncompute.InPlaceTarget (modulusWord)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits binaryEquiv)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.Partner (fourierRows)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths (fourierBankWord)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback
  (pathBankAction blockOutput)
open Recovery.Initialization.HistoryColumns (actualHistoryBankDensity)

/-- The first and second coordinates keep their original first/second exponent meanings. -/
def sourceCoefficient (width m r : Nat) (path : Fin (2 * m) → Branch width m)
    (source : Bits m × Bits m) : ℂ :=
  ((((if (binaryEquiv m source.2).val < r then invSqrt r else 0 : ℝ) : ℂ) *
      ((if (binaryEquiv m source.1).val < r then invSqrt r else 0 : ℝ) : ℂ)) *
    (fourierRows true m (blockOutput width m path true) source.2 *
      fourierRows true m (blockOutput width m path false) source.1))

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  {m : Nat}

/-- The literal arithmetic word at a fixed virtual source, surrounded by four conversions. -/
def sourceWord (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (source : Bits m × Bits m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size (modulusWord
    p) coefficient
      (ResidualReference p.size m Reference) *
    OrderedBankWord.exponentPair
      (pathBankAction (environment := environment) (m := m) E points Reference path false)
      (pathBankAction (environment := environment) (m := m) E points Reference path true)
      m (binaryEquiv m source.1).val (binaryEquiv m source.2).val *
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size (modulusWord
      p) coefficient⁻¹
      (ResidualReference p.size m Reference)

/-- The actual converted word is its coherent free-source sum, with no path summation yet. -/
lemma convertedFourierBankWord_source_sum (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m) :
    convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
      Reference path =
      ∑ source : Bits m × Bits m,
        sourceCoefficient p.size m r path source •
          sourceWord (environment := environment) (m := m) E points coefficient Reference path
            source := by
  calc
    _ = ∑ second : Bits m, ∑ first : Bits m,
        sourceCoefficient p.size m r path (first, second) •
          sourceWord (environment := environment) (m := m) E points coefficient Reference path
            (first, second) := by
      unfold convertedFourierBankWord fourierBankWord sourceCoefficient sourceWord
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Both source coordinates survive the CP sandwich for an arbitrary complete bank matrix. -/
lemma convertedFourierBankWord_sandwich (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (density : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ) :
    convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
      Reference path * density *
        (convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
          Reference path).conjTranspose =
      ∑ left : Bits m × Bits m, ∑ right : Bits m × Bits m,
        (sourceCoefficient p.size m r path left *
          star (sourceCoefficient p.size m r path right)) •
        (sourceWord (environment := environment) (m := m) E points coefficient Reference path left
          * density *
          (sourceWord (environment := environment) (m := m) E points coefficient Reference path
            right).conjTranspose) := by
  simp only [convertedFourierBankWord_source_sum]
  exact coherent_sandwich _ _ density

/-- Every legal actual path and complete source Store retains all coherent cross terms. -/
lemma outputBankDensity_source_quadratic (fieldTail : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (final : Store (Recovery.Layout.terminal p.size m)) :
    OutputBankDensity.outputBankDensity (environment := environment) E fieldTail m seed r points
      coefficient state
        predicate final =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            ∑ left : Bits m × Bits m, ∑ right : Bits m × Bits m,
              (sourceCoefficient p.size m r path left *
                star (sourceCoefficient p.size m r path right)) •
              (sourceWord (environment := environment) (m := m) E points coefficient Reference
                path left *
                actualHistoryBankDensity (environment := environment) E fieldTail m seed state
                  predicate original *
                (sourceWord (environment := environment) (m := m) E points coefficient Reference
                  path right).conjTranspose)
          else 0 := by
  unfold OutputBankDensity.outputBankDensity
  apply Finset.sum_congr rfl
  intro path _
  apply Finset.sum_congr rfl
  intro original _
  by_cases legal : traceValid p.size m (2 * m) id path original final
  · rw [if_pos legal, if_pos legal]
    exact convertedFourierBankWord_sandwich (m := m) E r points coefficient Reference path _
  · rw [if_neg legal, if_neg legal]

end

end CoherentBankFamily
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
