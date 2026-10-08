/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Readout
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Base.State.Density

/-!
# Born probability of the actual retained ECDLP sample

The measured output distribution is read from the actual finite cells and
has the Born fibers of the complete source vector. All unmeasured point codes
and arbitrary reference coordinates participate in the trace calculation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Interpret the real retained two-valued cells as the ordered exponent bits. -/
@[expose] public def observedOutcome (I : ECDLPInstance E)
    (value : (CShape.fixedVector (sampleWidth I) (.finite 2)).Value) :
    Fin (sampleWidth I) → Bool :=
  fun index => decide ((value.get index).toFin.val = 1)

/-- Exponent bits of a complete physical basis label, with the point bank retained. -/
@[expose] public def basisOutcome (I : ECDLPInstance E)
    (basis : (post I).register.Index) : Fin (sampleWidth I) → Bool :=
  fun index => decide ((basis (exponentPosition I index)).val = 1)

private theorem observedOutcome_after_measurement (I : ECDLPInstance E) (A : Access I)
    (stored : Store (post I)) (basis : (post I).register.Index) :
    observedOutcome I ((writtenStore I A stored basis).read (sampleInput I)) =
      basisOutcome I basis := by
  funext index
  change decide
    ((((writtenStore I A stored basis).read (.storage (cell I index).toCStorageRef)).toFin.val)
      = 1) = decide ((basis (exponentPosition I index)).val = 1)
  rw [writtenStore, measured_cell]

private theorem readoutCode_block_mass (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (post I) Reference ((executionModel I A).HiddenState × History))
    (outcome : Fin (sampleWidth I) → Bool) :
    ((((readoutCode I A).execute Reference state).mapClassical
      (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass =
      (∑ basis : (post I).register.Index,
        if basisOutcome I basis = outcome then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.measurementSequence_diagonalSum]
  change ExecutionState.diagonalSum state
    (fun record basis =>
      if observedOutcome I ((writtenStore I A record.1 basis.1).read (sampleInput I)) = outcome
      then 1 else 0) = _
  simp only [observedOutcome_after_measurement]
  refine (ExecutionState.diagonalSum_localMarginal state (fun basis =>
    if basisOutcome I basis = outcome then 1 else 0)).trans ?_
  apply Finset.sum_congr rfl
  intro basis _
  split <;> simp only [one_mul, zero_mul]

private theorem pure_diagonal_re {R : Register} (state : NormalizedVector R)
    (basis : R.Index) :
    ((DensityOperator.ofPure state).matrix basis basis).re = ‖state basis‖ ^ 2 := by
  rw [DensityOperator.ofPure_matrix]
  exact (congrArg Complex.re (Complex.mul_conj (state basis))).trans
    (Complex.normSq_eq_norm_sq (state basis))

/-- Each actual observed sample block has precisely its full source Born-fiber mass. -/
public theorem ecdlpSampling_code_block_mass (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (normalized : state.IsNormalized) (outcome : Fin (sampleWidth I) → Bool) :
    ((((code I A expansion).execute Reference state).mapClassical
      (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass =
      ∑ basis : (post I).register.Index,
        if basisOutcome I basis = outcome then ‖runtimeSourceState I A basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post I).register.Index,
        if basisOutcome I basis = outcome then
          ((beforeMeasurement I A expansion).execute Reference state).quantumMarginal.marginalLeft
            |>.matrix basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory,
        ExecutionState.executionState_mapClassical_comp, Function.comp_def] using
          readoutCode_block_mass I A ((beforeMeasurement I A expansion).execute Reference state)
            outcome
    _ = _ := by
      rw [ecdlpBeforeMeasurement_localDensity I A expansion state normalized, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepts : basisOutcome I basis = outcome
      · simp only [accepts, if_true, pure_diagonal_re]
      · simp only [accepts, if_false, Complex.zero_re]

/-- The actual run's retained output has the source Born probabilities. -/
public theorem ecdlpSampling_run_outputProbability (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register}
    (input : OracleInput (executionModel I A).classicalOracles (pre I) Reference)
    (outcome : Fin (sampleWidth I) → Bool) :
    ((run I A expansion).outputDistribution input).map (observedOutcome I) outcome =
      ENNReal.ofReal (∑ basis : (post I).register.Index,
        if basisOutcome I basis = outcome then ‖runtimeSourceState I A basis‖ ^ 2 else 0) := by
  have actual := congrArg (fun distribution : PMF (Fin (sampleWidth I) → Bool) =>
    distribution outcome)
    (ExecutionState.toPMF_mapClassical ((run I A expansion).execute Reference input.state)
      ((run I A expansion).execute_normalized input)
      (fun record => observedOutcome I ((run I A expansion).result record)))
  rw [AlgorithmRun.outputDistribution, PMF.map_comp]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    ((((code I A expansion).execute Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).mapClassical
        (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass = _
  rw [ecdlpSampling_code_block_mass I A expansion _
    (input.state.mapClassical_normalized input.normalized _)]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
