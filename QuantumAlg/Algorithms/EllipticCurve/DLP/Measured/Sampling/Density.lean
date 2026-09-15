/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Initialization

/-!
# Complete quantum density of a sampling round with arbitrary old classical cells

The original preparation, measured scalar cascade and inverse QFT act on the
already allocated systems. Their complete quantum-reference output on the
original good domain depends only on the input quantum marginal. All previous
classical cell values and mathematical histories remain arbitrary.

The initialized corollary asks for a quantum density equality that an actual
reset or preparation must establish. It neither supplies classical zero values
nor identifies complete classical-quantum states outside the good domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP ConcreteCircuitAccess GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original exponent preparation acts on the complete existing quantum register. -/
def samplingPreparedDensity (problem : KnownOrderProblem E.GroupPoint) (Reference : Register)
    (input : DensityOperator
      (Register.prod (after p.size (2 * orderWidth problem)).register Reference)) :
    DensityOperator (Register.prod (after p.size (2 * orderWidth problem)).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor
      (afterExponentProgram p (orderWidth problem) (exponentPreparationCircuit problem)
        (exponentPreparationCircuit_physical_idx problem)).matrix (1 : UnitaryOperator Reference))
    input

/-- The original three quantum stages prescribe the full target on the existing systems. -/
def samplingPrefixDensity (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (Reference : Register)
    (input : DensityOperator
      (Register.prod (after p.size (2 * orderWidth problem)).register Reference)) :
    DensityOperator (Register.prod (after p.size (2 * orderWidth problem)).register Reference) :=
  DensityOperator.applyUnitary
    (UnitaryOperator.prodTensor
      (afterExponentProgram p (orderWidth problem) (exponentReadoutCircuit problem)
        (exponentReadoutCircuit_physical_idx problem)).matrix (1 : UnitaryOperator Reference))
    (DensityOperator.applyUnitary
      (Encoding.placedConvertedTarget E points (List.finRange (2 * orderWidth problem))
        (Semantics.radixUnit p fieldTail.succ odd) Reference)
      (samplingPreparedDensity E problem Reference input))

/-- Actual measured execution on the good density needs no values for the old result cells. -/
theorem samplingPrefix_density_of_support (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (after p.size (2 * orderWidth problem)) Reference History)
    (support : cascadeSupport E points Reference (List.finRange (2 * orderWidth problem))
      (DensityOperator.applyUnitary
        (Encoding.pairOperator p.size (2 * orderWidth problem) (InPlaceTarget.modulusWord p)
          (Semantics.radixUnit p fieldTail.succ odd)⁻¹ Reference)
        ((samplingPreparedDensity E problem Reference state.quantumMarginal).reindex
          (ContextPermutation.referenceBasis
            (body_entries p.size (2 * orderWidth problem)) Reference).symm))) :
    ((samplingPrefix E fieldTail odd problem points).execute Reference state).quantumMarginal =
      samplingPrefixDensity E fieldTail odd problem points Reference state.quantumMarginal := by
  have prepared := afterExponentCircuit_density p (orderWidth problem)
    (exponentPreparationCircuit problem) (exponentPreparationCircuit_physical_idx problem) state
  have domain : cascadeSupport E points Reference (List.finRange (2 * orderWidth problem))
      (DensityOperator.applyUnitary
        (Encoding.pairOperator p.size (2 * orderWidth problem) (InPlaceTarget.modulusWord p)
          (Semantics.radixUnit p fieldTail.succ odd)⁻¹ Reference)
        ((((afterExponentCircuit p (orderWidth problem) (exponentPreparationCircuit problem)
          (exponentPreparationCircuit_physical_idx problem)).execute Reference state)
          |>.quantumMarginal).reindex
            (ContextPermutation.referenceBasis
              (body_entries p.size (2 * orderWidth problem)) Reference).symm)) := by
    rw [prepared]
    exact support
  have scalar := Encoding.placedConvertedCascade_density E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
    ((afterExponentCircuit p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem)).execute Reference state) domain
  rw [samplingPrefix, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    afterExponentReadout, afterExponentCircuit_density, Circuit.execute_seq,
    State.mapHistory_quantumMarginal, scalar, prepared]
  rfl

/-- Fixed quantum preparation suffices while every previous classical value remains arbitrary. -/
theorem samplingPrefix_density_of_initialized (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (after p.size (2 * orderWidth problem)) Reference History)
    (input : DensityOperator
      (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (same : state.quantumMarginal = initializedDensity p (2 * orderWidth problem) Reference input)
    (support : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference input).matrix basis basis = 0) :
    ((samplingPrefix E fieldTail odd problem points).execute Reference state).quantumMarginal =
      preMeasurementDensity E fieldTail odd problem points Reference input := by
  have prepared : samplingPreparedDensity E problem Reference state.quantumMarginal =
      initializedDensity p (2 * orderWidth problem) Reference
        (exponentPreparedDensity E problem Reference input) := by
    rw [same]
    exact afterExponentOperator_initializedDensity p (orderWidth problem)
      (exponentPreparationCircuit problem) (exponentPreparationCircuit_physical_idx problem)
      Reference input
  have domain := Encoding.convertedInitializedSupport_of_input_trajectory E points
    (List.finRange (2 * orderWidth problem)) (Semantics.radixUnit p fieldTail.succ odd)
    Reference (exponentPreparedDensity E problem Reference input) (by
      intro basis outside
      apply support basis
      rintro ⟨branch, equal, admissible⟩
      apply outside
      rw [equal]
      exact Encoding.pairedMontgomeryInput_convertedTrajectory E fieldTail sameWidth fits odd
        points seed branch admissible)
  have actual := samplingPrefix_density_of_support E fieldTail odd problem points state (by
    rw [prepared]
    exact domain)
  exact actual.trans (by
    unfold samplingPrefixDensity
    rw [prepared]
    rfl)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
