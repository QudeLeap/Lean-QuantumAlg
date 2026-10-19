/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.FamilyCompleteness
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Converted.WordCompleteness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.KrausEffects
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.SelectedBankProbability

/-!
# Selected effects of the complete actual legal free-source family

The existing rectangular Kraus effect is instantiated with the internally
proved Gram of the actual legal columns. A predicate selects full legal
labels without dropping zero CP outcomes or changing the final Store and
physical path coordinates. The whole coherent source and arbitrary retained
bank and Reference remain the effect's input space.

Final-Store events are the projection of these same labels. Their trace
pairing with each actual prepared history bank matrix is exactly the existing
bank event weight and, under the existing interval preparation bounds, the
actual reset-plus-converted execution's effectWeight. No incoming state is
normalized, divided by its mass, or assumed clean. The contraction certificate
requires no preparation bound, support condition or caller Gram hypothesis.

This module proves neither agreement on an ideal good component nor a success
floor. It changes no runtime, physical allocation or Algorithm contract.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualSelectedEffect

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (State Store)
open Recovery.Stage.PointCoordinates (ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open Recovery.Conversion (convertedStages)
open Recovery.Conversion.FreeSourceFamily
  (LegalOutcome sourceRegister legalColumns preparationColumns outputBankDensity_legalColumns)
open Recovery.Conversion.SelectedBankProbability
  (bankEventWeight actual_event_weight_eq_bankEventWeight)
open scoped BigOperators ComplexOrder

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

/-- Every predicate of the exact legal labels defines a certified effect on the whole source. -/
def legalEffect (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (original : Store (Recovery.Layout.terminal p.size m))
    (selected : LegalOutcome p m original → Prop) :
    Effect (sourceRegister p.size m Reference) :=
  KrausEffects.selectedEffect
    (Source := sourceRegister p.size m Reference)
    (Target := ConvertedWordCompleteness.bankRegister p.size
      (ResidualReference p.size m Reference))
    (legalColumns (environment := environment) E points coefficient Reference original)
    (ActualFamilyCompleteness.legalColumns_complete E points coefficient Reference original)
    selected

/-- The matrix is the selected sum of actual legal Kraus Grams, without cross-label terms. -/
lemma legalEffect_matrix (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (selected : LegalOutcome p m original → Prop) :
    (legalEffect (environment := environment) E points coefficient Reference original
      selected).matrix =
      ∑ outcome : LegalOutcome p m original,
        if selected outcome then
          (legalColumns (environment := environment) E points coefficient Reference original
            outcome).conjTranspose *
            legalColumns (environment := environment) E points coefficient Reference original
              outcome
        else 0 :=
  KrausEffects.selectedEffect_matrix
    (Source := sourceRegister p.size m Reference)
    (Target := ConvertedWordCompleteness.bankRegister p.size
      (ResidualReference p.size m Reference))
    (legalColumns (environment := environment) E points coefficient Reference original)
    (ActualFamilyCompleteness.legalColumns_complete E points coefficient Reference original)
    selected

/-- Positivity holds on every source and bank coordinate, including all dirty frame entries. -/
lemma legalEffect_positive (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (selected : LegalOutcome p m original → Prop) :
    (legalEffect (environment := environment) E points coefficient Reference original
      selected).matrix.PosSemidef :=
  (legalEffect (environment := environment) E points coefficient Reference original
    selected).positive

/-- The selected operator contracts every whole-source vector without a support hypothesis. -/
lemma legalEffect_contractive (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (selected : LegalOutcome p m original → Prop)
    (vector : HilbertVector (sourceRegister p.size m Reference)) :
    ‖(legalEffect (environment := environment) E points coefficient Reference original
      selected).matrix.applyVec vector‖ ≤
      ‖vector‖ :=
  (legalEffect (environment := environment) E points coefficient Reference original
    selected).contractive vector

/-- Exact selected CP trace pairing also holds for arbitrary, unnormalized source matrices. -/
lemma legalEffect_trace (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (selected : LegalOutcome p m original → Prop)
    (density : HilbertOperator (sourceRegister p.size m Reference)) :
    ((legalEffect (environment := environment) E points coefficient Reference original
      selected).matrix * density).trace.re =
      ∑ outcome : LegalOutcome p m original,
        if selected outcome then
          (legalColumns (environment := environment) E points coefficient Reference original
            outcome *
            density * (legalColumns (environment := environment) E points coefficient Reference
              original
              outcome).conjTranspose).trace.re
        else 0 := by
  rw [legalEffect_matrix]
  simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases chosen : selected outcome
  · simp only [if_pos chosen]
    congr 1
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  · simp only [if_neg chosen, zero_mul, Matrix.trace_zero, Complex.zero_re]

/-- The same exact trace pairing is the effect weight of every subnormalized mixed input. -/
lemma legalEffect_weight (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (selected : LegalOutcome p m original → Prop)
    (state : DensityOperator (sourceRegister p.size m Reference)) :
    (legalEffect (environment := environment) E points coefficient Reference original
      selected).weight state =
      ∑ outcome : LegalOutcome p m original,
        if selected outcome then
          (legalColumns (environment := environment) E points coefficient Reference original
            outcome *
            state.matrix * (legalColumns (environment := environment) E points coefficient
              Reference original
              outcome).conjTranspose).trace.re
        else 0 :=
  legalEffect_trace E points coefficient Reference original selected state.matrix

/-- The actual Store event selects precisely the final Store projection of each legal label. -/
def eventEffect (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (original : Store (Recovery.Layout.terminal p.size m))
    (event : Store (Recovery.Layout.terminal p.size m) → Prop) :
    Effect (sourceRegister p.size m Reference) :=
  legalEffect (environment := environment) E points coefficient Reference original (fun outcome =>
    event outcome.1)

/-- The final Store predicate is applied to every legal path belonging to that Store. -/
lemma eventEffect_matrix (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (event : Store (Recovery.Layout.terminal p.size m) → Prop) :
    (eventEffect (environment := environment) E points coefficient Reference original
      event).matrix =
      ∑ outcome : LegalOutcome p m original,
        if event outcome.1 then
          (legalColumns (environment := environment) E points coefficient Reference original
            outcome).conjTranspose *
            legalColumns (environment := environment) E points coefficient Reference original
              outcome
        else 0 :=
  legalEffect_matrix E points coefficient Reference original (fun outcome => event outcome.1)

/-- The event effect pairs with exactly the same selected legal CP output matrices. -/
lemma eventEffect_trace (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (event : Store (Recovery.Layout.terminal p.size m) → Prop)
    (density : HilbertOperator (sourceRegister p.size m Reference)) :
    ((eventEffect (environment := environment) E points coefficient Reference original
      event).matrix * density).trace.re =
      ∑ outcome : LegalOutcome p m original,
        if event outcome.1 then
          (legalColumns (environment := environment) E points coefficient Reference original
            outcome *
            density * (legalColumns (environment := environment) E points coefficient Reference
              original
              outcome).conjTranspose).trace.re
        else 0 :=
  legalEffect_trace E points coefficient Reference original (fun outcome => event outcome.1) density

/-- The existing bank event weight is the event effect on each same actual history source matrix. -/
lemma bankEventWeight_eq_eventEffect_trace (fieldTail : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (event : Store (Recovery.Layout.terminal p.size m) → Prop) :
    bankEventWeight (environment := environment) E fieldTail m seed r points coefficient
        state predicate event =
      ∑ original : Store (Recovery.Layout.terminal p.size m),
        ((eventEffect (environment := environment) E points coefficient Reference original
          event).matrix *
          (preparationColumns p.size m r Reference *
            Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment :=
              environment) E fieldTail m seed
              state predicate original *
            (preparationColumns p.size m r Reference).conjTranspose)).trace.re
        := by
  let prepared := fun original : Store (Recovery.Layout.terminal p.size m) =>
    preparationColumns p.size m r Reference *
      Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment := environment)
        E fieldTail m seed
        state predicate original *
      (preparationColumns p.size m r Reference).conjTranspose
  unfold bankEventWeight
  calc
    _ = ∑ final : Store (Recovery.Layout.terminal p.size m),
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          ∑ path : {path : Fin (2 * m) → Branch p.size m //
              traceValid p.size m (2 * m) id path original final},
            if event final then
              (legalColumns (environment := environment) E points coefficient Reference original
                ⟨final, path⟩ * prepared original *
                (legalColumns (environment := environment) E points coefficient Reference original
                  ⟨final, path⟩).conjTranspose).trace.re
            else 0 := by
      apply Finset.sum_congr rfl
      intro final _
      by_cases chosen : event final
      · rw [if_pos chosen, outputBankDensity_legalColumns]
        simp only [Matrix.trace_sum, Complex.re_sum, if_pos chosen, prepared]
      · simp only [if_neg chosen, Finset.sum_const_zero]
    _ = ∑ original : Store (Recovery.Layout.terminal p.size m),
        ∑ final : Store (Recovery.Layout.terminal p.size m),
          ∑ path : {path : Fin (2 * m) → Branch p.size m //
              traceValid p.size m (2 * m) id path original final},
            if event final then
              (legalColumns (environment := environment) E points coefficient Reference original
                ⟨final, path⟩ * prepared original *
                (legalColumns (environment := environment) E points coefficient Reference original
                  ⟨final, path⟩).conjTranspose).trace.re
            else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro original _
      simpa only [Fintype.sum_sigma, prepared] using
        (eventEffect_trace E points coefficient Reference original event (prepared original)).symm

/-- The same actual reset-plus-stream output event is represented by these source effects. -/
lemma actual_event_weight_eq_eventEffect_trace (fieldTail : Nat) (seed : AffinePoint E)
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
        ((eventEffect (environment := environment) E points coefficient Reference original
          event).matrix *
          (preparationColumns p.size m r Reference *
            Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment :=
              environment) E fieldTail m seed
              state predicate original *
            (preparationColumns p.size m r Reference).conjTranspose)).trace.re :=
  (actual_event_weight_eq_bankEventWeight E fieldTail m seed r
    points coefficient state predicate event positive fits).trans
    (bankEventWeight_eq_eventEffect_trace E fieldTail seed r points coefficient
      state predicate event)

end

end ActualSelectedEffect
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
