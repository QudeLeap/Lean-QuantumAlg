/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Readout
import all QuantumAlg.Primitives.ZReset.Bank.Read
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Base.State.Density

/-!
# Actual reused sample probabilities after its terminal physical reset

The real exponent writes give the original full Born fibers, scaled by the
incoming probability mass. The actual terminal reset cannot write those
cells and preserves their probabilities. This law applies directly to every
subnormalized failure fiber of the real checked-recovery loop.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

open Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] reset sampleInput
attribute [local irreducible] context Sampling.sampleWidth

/-- The original exponent interpretation on this round's unchanged physical bank. -/
public def basisOutcome (I : ECDLPInstance E) :
    (context I).register.Index → Fin (sampleWidth I) → Bool :=
  fun basis index => decide ((basis (exponentPosition I index)).val = 1)

private theorem pure_diagonal_re {R : Register} (state : NormalizedVector R)
    (basis : R.Index) :
    ((DensityOperator.ofPure state).matrix basis basis).re = ‖state basis‖ ^ 2 := by
  rw [DensityOperator.ofPure_matrix]
  exact (congrArg Complex.re (Complex.mul_conj (state basis))).trans
    (Complex.normSq_eq_norm_sq (state basis))

private theorem scratch_separate (I : ECDLPInstance E) :
    (scratch I).key ∉ (sampleInput I).storageKeys := by
  change (Sampling.post I).canonicalFreshKey ∉
    ((Sampling.sampleInput I).underRetained (Sampling.post I).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I))).storageKeys
  exact CInputRef.fresh_not_mem_storageKeys_underRetained (Sampling.sampleInput I)
    (Sampling.post I).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I))

private theorem readouts_nodup (I : ECDLPInstance E) :
    ((readouts I).map fun item => item.output.key).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  simp only [Function.comp_def, readout, QubitReadouts.readout_key] at same
  change (Sampling.cell I left).key = (Sampling.cell I right).key at same
  exact MeasurementCells.reference_key_injective (Sampling.bankContext I) 2 (sampleWidth I) same

private theorem measured_cell (I : ECDLPInstance E) (A : Access I)
    (stored : Store (context I)) (basis : (context I).register.Index)
    (index : Fin (sampleWidth I)) :
    ((Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := model I A)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts I) stored
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := model I A)
        (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
        (readouts I) basis)).read (.storage (cell I index).toCStorageRef)).toFin.val =
      (basis (exponentPosition I index)).val := by
  have actual := Circuit.writeMeasurementBasis_read (gates := AlgorithmGate.model)
    (oracles := model I A) (operations := BitWord.model) (services := ClassicalOracleModel.empty)
    (readouts I) (readouts_nodup I) (readout I index)
    (List.mem_ofFn.mpr ⟨index, rfl⟩) stored basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  simp only [readout, QubitReadouts.readout] at numeric
  rw [QubitReadouts.outputAt_read] at numeric
  exact numeric

private theorem observed_after_measurement (I : ECDLPInstance E) (A : Access I)
    (stored : Store (context I)) (basis : (context I).register.Index) :
    observedOutcome I ((Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (oracles := model I A) (operations := BitWord.model)
      (classicalOracles := ClassicalOracleModel.empty) (readouts I) stored
        (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := model I A)
          (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
          (readouts I) basis)).read (sampleInput I)) = basisOutcome I basis := by
  funext index
  have actual := congrArg (fun value : Nat => decide (value = 1))
    (measured_cell I A stored basis index)
  exact actual

/-- The final actual reset retains every real exponent outcome fiber unchanged. -/
public theorem ecdlpReuse_reset_outcome_mass (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History))
    (outcome : Fin (sampleWidth I) → Bool) :
    ((((reset I A).execute Reference state).mapClassical
      (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass =
      ((state.mapClassical
        (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass := by
  dsimp only [reset]
  exact ZReset.Bank.zResetBank_decoded_read_mass (ctx := context I) (oracles := model I A)
    (ecdlpReuse_qubits I) (scratch I) BitWord.model (sampleInput I) (scratch_separate I)
    (observedOutcome I) outcome state

private theorem readout_mass (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History))
    (outcome : Fin (sampleWidth I) → Bool) :
    ((((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := model I A)
      (operations := BitWord.model) (classicalOracles := ClassicalOracleModel.empty)
      (readouts I)).execute Reference state).mapClassical
        (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass =
      (∑ basis : (context I).register.Index,
        if basisOutcome I basis = outcome then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [Circuit.measurementSequence_diagonalSum]
  simp only [observed_after_measurement]
  refine (ExecutionState.diagonalSum_localMarginal state (fun basis =>
    if basisOutcome I basis = outcome then 1 else 0)).trans ?_
  apply Finset.sum_congr rfl
  intro basis _
  split <;> simp only [one_mul, zero_mul]

/-- The same full round returns the source Born fibers at the real incoming mass. -/
public theorem ecdlpReuse_code_outcome_mass (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History))
    (outcome : Fin (sampleWidth I) → Bool) :
    ((((code I A expansion).execute Reference state).mapClassical
      (fun record => observedOutcome I (record.1.read (sampleInput I)))).block outcome).mass =
      state.mass * ∑ basis : (context I).register.Index,
        if basisOutcome I basis = outcome then
          ‖runtimeSourceState I A basis‖ ^ 2 else 0 := by
  have density := ecdlpReuse_beforeReadout_matrix I A expansion state
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal] at density
  rw [code, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  rw [ecdlpReuse_reset_outcome_mass, readout_mass, density, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro basis _
  by_cases selected : basisOutcome I basis = outcome
  · simp only [selected, if_true, Matrix.smul_apply, Complex.smul_re, smul_eq_mul,
      pure_diagonal_re]
  · simp only [selected, if_false, Complex.zero_re, mul_zero]

/-- The actual full round returns the source probabilities after both physical resets. -/
public theorem ecdlpReuse_run_outputProbability (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register}
    (input : OracleInput (executionModel I A).classicalOracles (context I) Reference)
    (outcome : Fin (sampleWidth I) → Bool) :
    ((run I A expansion).outputDistribution input).map (observedOutcome I) outcome =
      ENNReal.ofReal (∑ basis : (context I).register.Index,
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
  rw [ecdlpReuse_code_outcome_mass, ExecutionState.mapClassical_mass, input.normalized, one_mul]

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
