/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Selected.Effect
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.History.Reference

/-!
# The actual selected event retains the original mixed Reference masses

The actual event effect pairs with the same preparation columns and the same
initialized seed slice of each selected complete Store. The existing Reference
spectral decomposition expands that literal trace into pure Reference traces.
There is no normalization by a branch mass, and every original Store remains
a separate outer summand even when its reset seed coordinates coincide.

The last lemma only lifts an internal bound on these exact pure components.
The original good-component comparison and selected floor must still prove
that bound. This module introduces no algorithm certificate, runtime object,
new spectral construction, or old execution retirement claim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualReferenceEvent

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
open Recovery.Conversion
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

/-- The same actual event, preparation and initialized seed column for a pure Reference. -/
def referenceComponentWeight (fieldTail : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} (original : Store (Recovery.Layout.terminal p.size m))
    (event : Store (Recovery.Layout.terminal p.size m) → Prop)
    (input : NormalizedVector Reference) : ℝ :=
  ((ActualSelectedEffect.eventEffect (environment := environment) E points coefficient Reference
    original event).matrix *
    (FreeSourceFamily.preparationColumns p.size m r Reference *
      (DensityOperator.ofPure
        (NormalizedVector.prodTensor
          (NormalizedVector.ket (Recovery.Initialization.newResetLabel E fieldTail m seed))
          input)).matrix.submatrix
            (initializedBasis p.size m Reference) (initializedBasis p.size m Reference) *
      (FreeSourceFamily.preparationColumns p.size m r Reference).conjTranspose)).trace.re

/-- Each complete original Store keeps its exact Reference spectral coefficients. -/
lemma originalStore_spectral_weight (fieldTail : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (original : Store (Recovery.Layout.terminal p.size m))
    (event : Store (Recovery.Layout.terminal p.size m) → Prop) :
    ((ActualSelectedEffect.eventEffect (environment := environment) E points coefficient Reference
      original event).matrix *
      (FreeSourceFamily.preparationColumns p.size m r Reference *
        Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment :=
          environment) E fieldTail m seed
          state predicate original *
        (FreeSourceFamily.preparationColumns p.size m r Reference).conjTranspose)).trace.re =
      ∑ index : Reference.Index,
        (Recovery.Initialization.HistoryReference.referenceDensity (environment := environment) E
          fieldTail m seed
          state predicate original).spectralMass index *
        referenceComponentWeight (environment := environment) E fieldTail seed r points
          coefficient original event
          ((Recovery.Initialization.HistoryReference.referenceDensity (environment := environment)
            E fieldTail m seed
            state predicate original).spectralVector index) := by
  rw [Recovery.Initialization.HistoryReference.actualHistoryBankDensity_spectral]
  simp only [referenceComponentWeight, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.smul_re,
    smul_eq_mul]

/-- The existing bank event weight is the full Store by Reference spectral sum. -/
lemma bankEventWeight_eq_reference_spectral (fieldTail : Nat) (seed : AffinePoint E)
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (event : Store (Recovery.Layout.terminal p.size m) → Prop) :
    SelectedBankProbability.bankEventWeight (environment := environment) E fieldTail m seed r
      points coefficient
        state predicate event =
      ∑ original : Store (Recovery.Layout.terminal p.size m),
        ∑ index : Reference.Index,
          (Recovery.Initialization.HistoryReference.referenceDensity (environment := environment)
            E fieldTail m seed
            state predicate original).spectralMass index *
          referenceComponentWeight (environment := environment) E fieldTail seed r points
            coefficient original event
            ((Recovery.Initialization.HistoryReference.referenceDensity (environment :=
              environment) E fieldTail m seed
              state predicate original).spectralVector index) := by
  rw [ActualSelectedEffect.bankEventWeight_eq_eventEffect_trace]
  apply Finset.sum_congr rfl
  intro original _
  exact originalStore_spectral_weight E fieldTail seed r points coefficient
    state predicate original event

/-- The same literal reset-plus-converted event has this original-mass expansion. -/
lemma actual_event_weight_eq_reference_spectral (fieldTail : Nat) (seed : AffinePoint E)
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (event : Store (Recovery.Layout.terminal p.size m) → Prop)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute environment
      Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
        state)).effectWeight
        (fun record => if predicate record.2.2.1.1 ∧ event record.1 then
          Effect.one ((Recovery.Layout.terminal p.size m).register.prod Reference)
        else Effect.zero ((Recovery.Layout.terminal p.size m).register.prod Reference)) =
      ∑ original : Store (Recovery.Layout.terminal p.size m),
        ∑ index : Reference.Index,
          (Recovery.Initialization.HistoryReference.referenceDensity (environment := environment)
            E fieldTail m seed
            state predicate original).spectralMass index *
          referenceComponentWeight (environment := environment) E fieldTail seed r points
            coefficient original event
            ((Recovery.Initialization.HistoryReference.referenceDensity (environment :=
              environment) E fieldTail m seed
              state predicate original).spectralVector index) :=
  (SelectedBankProbability.actual_event_weight_eq_bankEventWeight E fieldTail m seed r
    points coefficient state predicate event positive fits).trans
    (bankEventWeight_eq_reference_spectral E fieldTail seed r points coefficient
      state predicate event)

/-- An internal uniform pure-component bound retains this complete Store's original mass. -/
lemma originalStore_mass_mul_le (fieldTail : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (original : Store (Recovery.Layout.terminal p.size m))
    (event : Store (Recovery.Layout.terminal p.size m) → Prop) (lower : ℝ)
    (bound : ∀ input : NormalizedVector Reference,
      lower ≤ referenceComponentWeight (environment := environment) E fieldTail seed r points
        coefficient original event input) :
    (Recovery.Initialization.HistoryReference.selectedStoreDensity (environment := environment) E
      fieldTail m seed
      state predicate original).mass * lower ≤
      ((ActualSelectedEffect.eventEffect (environment := environment) E points coefficient
        Reference original event).matrix *
        (FreeSourceFamily.preparationColumns p.size m r Reference *
          Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment :=
            environment) E fieldTail m seed
            state predicate original *
          (FreeSourceFamily.preparationColumns p.size m r Reference).conjTranspose)).trace.re := by
  rw [originalStore_spectral_weight,
    ← Recovery.Initialization.HistoryReference.referenceDensity_mass E fieldTail m seed
      state predicate original]
  let density := Recovery.Initialization.HistoryReference.referenceDensity (environment :=
    environment) E fieldTail m seed
    state predicate original
  change density.mass * lower ≤ ∑ index : Reference.Index,
    density.spectralMass index * referenceComponentWeight (environment := environment) E fieldTail
      seed r points coefficient
      original event (density.spectralVector index)
  rw [← density.sum_spectralMass, Finset.sum_mul]
  exact Finset.sum_le_sum (fun index _ =>
    mul_le_mul_of_nonneg_left (bound (density.spectralVector index))
      (density.spectralMass_nonneg index))

/-- Pure-component bounds lift to the actual event with every original Store still separate. -/
lemma actual_event_weight_ge_selected_mass (fieldTail : Nat) (seed : AffinePoint E)
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (event : Store (Recovery.Layout.terminal p.size m) → Prop)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) (lower : ℝ)
    (bound : ∀ original : Store (Recovery.Layout.terminal p.size m),
      ∀ input : NormalizedVector Reference,
        lower ≤ referenceComponentWeight (environment := environment) E fieldTail seed r points
          coefficient
          original event input) :
    (∑ original : Store (Recovery.Layout.terminal p.size m),
      (Recovery.Initialization.HistoryReference.selectedStoreDensity (environment := environment)
        E fieldTail m seed
        state predicate original).mass) * lower ≤
      ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute environment
        Reference
        ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
          state)).effectWeight
          (fun record => if predicate record.2.2.1.1 ∧ event record.1 then
            Effect.one ((Recovery.Layout.terminal p.size m).register.prod Reference)
          else Effect.zero ((Recovery.Layout.terminal p.size m).register.prod Reference)) := by
  rw [ActualSelectedEffect.actual_event_weight_eq_eventEffect_trace E fieldTail seed r
    points coefficient state predicate event positive fits, Finset.sum_mul]
  exact Finset.sum_le_sum (fun original _ =>
    originalStore_mass_mul_le E fieldTail seed r points coefficient state predicate
      original event lower (bound original))

end

end ActualReferenceEvent
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
