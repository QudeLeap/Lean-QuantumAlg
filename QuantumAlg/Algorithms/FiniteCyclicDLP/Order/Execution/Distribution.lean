/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Laws
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Probability
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Trace-derived output law of the known-order sampler

The distribution read from the actual retained cells is the Born distribution
of the same native-dimensional circuit used by execution and accounting.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExecution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The actual terminal measurements place exactly the corresponding Born
fiber in each observed-output block. -/
public theorem readoutCode_block_mass (P : KnownOrderProblem G)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (post P) Reference ((model P).HiddenState × H))
    (outcome : TerminalZMeasure.Outcome (sampleWidth P)) :
    ((((readoutCode P).execute Reference state).mapClassical
      (fun value => observedOutcome P (value.1.read (sampleInput P)))).block outcome).mass =
      (∑ basis : (post P).register.Index,
        if OrderBornBridge.readout P (basisEquiv P basis) = outcome then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.measurementSequence_diagonalSum]
  simp only [observedOutcome_after_measurement]
  calc
    _ = ∑ basis : (post P).register.Index,
        (if OrderBornBridge.readout P (basisEquiv P basis) = outcome
          then (1 : Complex) else 0) *
            state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if OrderBornBridge.readout P (basisEquiv P basis) = outcome then 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro basis _
      split <;> simp only [one_mul, zero_mul]

private theorem pure_diagonal_re {R : Register} (state : NormalizedVector R)
    (basis : R.Index) :
    ((DensityOperator.ofPure state).matrix basis basis).re = ‖state basis‖ ^ 2 := by
  rw [DensityOperator.ofPure_matrix]
  exact (congrArg Complex.re (Complex.mul_conj (state basis))).trans
    (Complex.normSq_eq_norm_sq (state basis))

/-- Every output block of the complete circuit has the source Born-fiber mass. -/
public theorem code_block_mass (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference ((model P).HiddenState × H))
    (normalized : state.IsNormalized)
    (outcome : TerminalZMeasure.Outcome (sampleWidth P)) :
    (((code P expansion).execute Reference state).mapClassical
      (fun value => observedOutcome P (value.1.read (sampleInput P)))
      |>.block outcome).mass =
      ∑ basis : (OrderOracle.layout P).Basis,
        if OrderBornBridge.readout P basis = outcome then
          ‖OrderBornBridge.evolvedState P expansion basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post P).register.Index,
        if OrderBornBridge.readout P (basisEquiv P basis) = outcome then
          ((beforeMeasurement P expansion).execute Reference state).quantumMarginal.marginalLeft
            |>.matrix basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory,
        ExecutionState.executionState_mapClassical_comp, Function.comp_def] using
          readoutCode_block_mass P
            ((beforeMeasurement P expansion).execute Reference state) outcome
    _ = (∑ basis : (OrderOracle.layout P).Basis,
        if OrderBornBridge.readout P basis = outcome then
          (DensityOperator.ofPure (OrderBornBridge.evolvedState P expansion)).matrix basis basis
        else 0).re := by
      rw [beforeMeasurement_localDensity P expansion state normalized]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm]
      exact (basisEquiv P).sum_comp (fun basis : (OrderOracle.layout P).Basis =>
        if OrderBornBridge.readout P basis = outcome then
          (DensityOperator.ofPure (OrderBornBridge.evolvedState P expansion)).matrix basis basis
        else 0)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted : OrderBornBridge.readout P basis = outcome
      · simp only [accepted, if_true, pure_diagonal_re]
      · simp only [accepted, if_false, Complex.zero_re]

/-- The output of the complete single-cycle run has exactly the circuit's
native-dimensional Born law. -/
public theorem run_outputDistribution (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    {Reference : Register}
    (input : OracleInput (model P).classicalOracles pre Reference) :
    ((run P expansion).outputDistribution input).map (observedOutcome P) =
      OrderBornBridge.outcomePMF P expansion := by
  apply PMF.ext
  intro outcome
  have actual := congrArg
    (fun distribution : PMF (TerminalZMeasure.Outcome (sampleWidth P)) =>
      distribution outcome)
    (ExecutionState.toPMF_mapClassical ((run P expansion).execute Reference input.state)
      ((run P expansion).execute_normalized input)
      (fun record => observedOutcome P ((run P expansion).result record)))
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution, PMF.map_comp]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    ((((code P expansion).execute Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).mapClassical
        (fun value => observedOutcome P (value.1.read (sampleInput P)))
      |>.block outcome).mass) = _
  rw [code_block_mass P expansion _
    (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  rw [OrderBornBridge.outcomePMF_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro basis _
  by_cases accepted : OrderBornBridge.readout P basis = outcome
  · simp only [accepted, if_true]
  · simp only [accepted, if_false, ENNReal.ofReal_zero]

end

end QuantumAlg.FiniteCyclicDLP.OrderExecution
