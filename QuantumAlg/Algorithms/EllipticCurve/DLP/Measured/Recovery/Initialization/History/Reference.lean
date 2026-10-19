/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.History.Columns
import all QuantumAlg.Core.Base.Gate.Effect.FixedInput
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# The actual selected reset bank has the same mixed Reference coefficients

Select the original History predicate and one complete Store in the actual
reset output. Its principal Reference slice retains exactly that fiber's
mass. Its spectral decomposition therefore gives the bank matrix as a sum
of pure Reference components on the same literal seed, with no conditional
normalization and no loss of off-diagonal entries.

The final lemma only lifts an internal uniform pure-Reference effect bound.
It does not supply that bound, identify a prepared Fourier event effect, or
assert a protocol success floor. Those remaining mathematical identities
must instantiate this lemma before any old execution proof can be removed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
namespace HistoryReference

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage.PointCoordinates.StageWord.PathWord
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)
variable {Reference : Register} {History : Type} [Fintype History]

/-- The same selected actual output, retaining its complete quantum-reference marginal. -/
def selectedStoreDensity
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    DensityOperator ((Recovery.Layout.terminal p.size m).register.prod Reference) :=
  ((((newReset E fieldTail m seed).execute environment Reference state).filterClassical
    (fun record => predicate record.2.2.1)).filterClassical
      (fun record => record.1 = stored)).quantumMarginal

/-- The actual seed slice is a positive subnormalized Reference density, without division. -/
def referenceDensity
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    DensityOperator Reference :=
  (selectedStoreDensity (environment := environment) E fieldTail m seed state predicate
    stored).basisSlice
    (newResetLabel E fieldTail m seed)

/-- Every selected full entry has exactly this actual seed and the same Reference coefficient. -/
lemma selectedStoreDensity_factor
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m))
    (left right : (Recovery.Layout.terminal p.size m).register.Index)
    (refLeft refRight : Reference.Index) :
    (selectedStoreDensity (environment := environment) E fieldTail m seed state predicate
      stored).matrix
        (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) left *
        (referenceDensity (environment := environment) E fieldTail m seed state predicate
          stored).matrix refLeft refRight *
        star (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) right) := by
  exact (HistoryColumns.actual_history_store_seeded E fieldTail m seed state predicate
    stored left right refLeft refRight).trans
      (BasisSeeded.ket_factor (newResetLabel E fieldTail m seed) left right
        ((referenceDensity (environment := environment) E fieldTail m seed state predicate
          stored).matrix refLeft refRight)).symm

/-- The Reference slice keeps the same selected Store mass, including zero. -/
lemma referenceDensity_mass
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    (referenceDensity (environment := environment) E fieldTail m seed state predicate stored).mass =
      (selectedStoreDensity (environment := environment) E fieldTail m seed state predicate
        stored).mass :=
  DensityOperator.basisSlice_mass_of_factor _ (newResetLabel E fieldTail m seed)
    (selectedStoreDensity_factor E fieldTail m seed state predicate stored)

private lemma ket_reference_spectral {R Reference : Register}
    (label : R.Index) (density : DensityOperator Reference)
    (left right : R.Index) (refLeft refRight : Reference.Index) :
    NormalizedVector.ket (R := R) label left * density.matrix refLeft refRight *
        star (NormalizedVector.ket (R := R) label right) =
      ∑ index : Reference.Index, density.spectralMass index •
        (DensityOperator.ofPure (NormalizedVector.prodTensor (NormalizedVector.ket label)
          (density.spectralVector index))).matrix (left, refLeft) (right, refRight) := by
  have spectral := congrArg (fun matrix : HilbertOperator Reference => matrix refLeft refRight)
    density.matrix_eq_sum_spectral
  simp only [Matrix.sum_apply, Matrix.smul_apply] at spectral
  rw [spectral, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  simp only [DensityOperator.ofPure_matrix, NormalizedVector.prodTensor_apply,
    Complex.real_smul, star_mul]
  ring

/-- The full selected physical density has its original-mass pure Reference spectral sum. -/
lemma selectedStoreDensity_spectral
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    (selectedStoreDensity (environment := environment) E fieldTail m seed state predicate
      stored).matrix =
      ∑ index : Reference.Index,
        (referenceDensity (environment := environment) E fieldTail m seed state predicate
          stored).spectralMass index •
          (DensityOperator.ofPure
            (NormalizedVector.prodTensor (NormalizedVector.ket (newResetLabel E fieldTail m seed))
              ((referenceDensity (environment := environment) E fieldTail m seed state predicate
                stored).spectralVector
                index))).matrix := by
  ext ⟨left, refLeft⟩ ⟨right, refRight⟩
  rw [selectedStoreDensity_factor]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  exact ket_reference_spectral (newResetLabel E fieldTail m seed)
    (referenceDensity (environment := environment) E fieldTail m seed state predicate stored) left
      right refLeft refRight

/-- The actual initialized bank uses these same components, not a new bank density or input. -/
lemma actualHistoryBankDensity_spectral
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    HistoryColumns.actualHistoryBankDensity (environment := environment) E fieldTail m seed state
      predicate stored =
      ∑ index : Reference.Index,
        (referenceDensity (environment := environment) E fieldTail m seed state predicate
          stored).spectralMass index •
          (DensityOperator.ofPure
            (NormalizedVector.prodTensor (NormalizedVector.ket (newResetLabel E fieldTail m seed))
              ((referenceDensity (environment := environment) E fieldTail m seed state predicate
                stored).spectralVector
                index))).matrix.submatrix
            (initializedBasis p.size m Reference) (initializedBasis p.size m Reference) := by
  ext row column
  change (selectedStoreDensity (environment := environment) E fieldTail m seed state predicate
    stored).matrix
    (initializedBasis p.size m Reference row) (initializedBasis p.size m Reference column) = _
  rw [selectedStoreDensity_spectral]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]

/-- Uniform pure Reference weights lift to the same arbitrary mixed selected reset fiber. -/
lemma mass_mul_le_weight_of_pure_reference
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m))
    (effect : Effect ((Recovery.Layout.terminal p.size m).register.prod Reference)) (lower : ℝ)
    (bound : ∀ input : NormalizedVector Reference, lower ≤ effect.weight
      (DensityOperator.ofPure
        (NormalizedVector.prodTensor (NormalizedVector.ket (newResetLabel E fieldTail m seed))
          input))) :
    (selectedStoreDensity (environment := environment) E fieldTail m seed state predicate
      stored).mass * lower ≤
      effect.weight (selectedStoreDensity (environment := environment) E fieldTail m seed state
        predicate stored) := by
  apply Effect.mass_mul_le_weight_of_basis_factor effect _ (newResetLabel E fieldTail m seed)
    lower (selectedStoreDensity_factor E fieldTail m seed state predicate stored)
  intro input
  rw [Effect.basisSliceEffect_weight_of_pure effect (newResetLabel E fieldTail m seed) input
    (NormalizedVector.prodTensor (NormalizedVector.ket (newResetLabel E fieldTail m seed)) input)
    (fun _ _ => rfl)]
  exact bound input

end

end HistoryReference
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
