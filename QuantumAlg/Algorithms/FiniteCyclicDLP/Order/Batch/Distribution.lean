/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.State
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Observation
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Laws
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.Probability
public import QuantumAlg.Util.PMF
public import QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Observation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Laws
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.Probability
import all QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Execution.Measurement.Distribution
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Independent Born law of the fresh-bank product state

The complete physical basis is equivalent to a fixed-length vector of source
bases.  Mapping independent source-basis draws through this equivalence gives
the exact product-state basis law, and terminally reading every bank gives the
independent vector of the one-cycle Born law.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Fixed-length vectors and finite-indexed source-bank families carry the
same coordinates in the same order. -/
@[expose] public def vectorFamilyEquiv (P : KnownOrderProblem G) (count : Nat) :
    List.Vector (OrderOracle.layout P).Basis count ≃
      (familyRegister P count).Index where
  toFun samples := samples.get
  invFun family := List.Vector.ofFn family
  left_inv samples := by
    apply List.Vector.ext
    intro slot
    simp
  right_inv family := by
    funext slot
    simp

/-- A vector of source-bank labels reassembles into the corresponding complete
physical family label. -/
@[expose] public def physicalBasisEquiv (P : KnownOrderProblem G) (count : Nat) :
    List.Vector (OrderOracle.layout P).Basis count ≃ (layout P count).Basis :=
  (vectorFamilyEquiv P count).trans (familyBasisEquiv P count).symm

@[simp] public lemma physicalBasisEquiv_symm_get (P : KnownOrderProblem G)
    (count : Nat) (basis : (layout P count).Basis) (slot : Fin count) :
    ((physicalBasisEquiv P count).symm basis).get slot = bankBasis P slot basis := by
  unfold physicalBasisEquiv
  rw [Equiv.symm_trans_apply]
  rw [Equiv.symm_symm]
  change
    (vectorFamilyEquiv P count
      ((vectorFamilyEquiv P count).symm ((familyBasisEquiv P count) basis))) slot =
        (familyBasisEquiv P count basis) slot
  exact congrFun
    ((vectorFamilyEquiv P count).apply_symm_apply ((familyBasisEquiv P count) basis)) slot

/-- Exact product-state computational-basis law on the actual family layout. -/
@[expose] public def physicalBasisPMF (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) : PMF (layout P count).Basis :=
  (PMF.independentReplicateVector (OrderBornBridge.basisPMF P expansion) count).map
    (physicalBasisEquiv P count)

/-- Every complete physical-basis mass is the product of the corresponding
one-cycle source-basis masses. -/
public lemma physicalBasisPMF_apply (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (basis : (layout P count).Basis) :
    physicalBasisPMF P count expansion basis =
      ∏ slot : Fin count,
        ENNReal.ofReal
          (‖OrderBornBridge.evolvedState P expansion (bankBasis P slot basis)‖ ^ 2) := by
  let samples := (physicalBasisEquiv P count).symm basis
  calc
    physicalBasisPMF P count expansion basis =
        physicalBasisPMF P count expansion
          (physicalBasisEquiv P count samples) := by
      rw [(physicalBasisEquiv P count).apply_symm_apply basis]
    _ = PMF.independentReplicateVector
          (OrderBornBridge.basisPMF P expansion) count samples := by
      exact PMF.map_apply_of_injective _ (physicalBasisEquiv P count)
        (physicalBasisEquiv P count).injective samples
    _ = ∏ slot : Fin count,
          OrderBornBridge.basisPMF P expansion (samples.get slot) := by
      exact PMF.independentReplicateVector_apply_prod _ count samples
    _ = _ := by
      apply Finset.prod_congr rfl
      intro slot _
      rw [OrderBornBridge.basisPMF_apply]
      rw [physicalBasisEquiv_symm_get]

/-- Terminally observing the exact product state gives independent copies of
the source circuit's Born distribution. -/
public lemma physicalBasisPMF_map_observedBasisVector
    (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    (physicalBasisPMF P count expansion).map (observedBasisVector P count) =
      PMF.independentReplicateVector (OrderBornBridge.outcomePMF P expansion) count := by
  rw [physicalBasisPMF, PMF.map_comp]
  have observation :
      observedBasisVector P count ∘ physicalBasisEquiv P count =
        fun samples => samples.map (OrderBornBridge.readout P) := by
    funext samples
    apply List.Vector.ext
    intro slot
    simp only [Function.comp_apply, observedBasisVector, List.Vector.get_ofFn,
      List.Vector.get_map]
    rw [← physicalBasisEquiv_symm_get P count
      (physicalBasisEquiv P count samples) slot]
    rw [(physicalBasisEquiv P count).symm_apply_apply]
  rw [observation, PMF.independentReplicateVector_map]
  rfl

/-- Terminal measurements place exactly the corresponding family Born fiber
in each observed-vector block. -/
public lemma readoutCode_block_mass (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (post P count) Reference ((OrderExecution.model P).HiddenState × H))
    (outcome : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count) :
    ((((readoutCode P count).execute
      (OrderExecution.sourceEnvironment P) Reference state).mapClassical
      (fun value => observedVector P count
        (value.1.read (samplesInput P count)))).block outcome).mass =
      (∑ basis : (post P count).register.Index,
        if observedBasisVector P count (basisEquiv P count basis) = outcome then
          state.quantumMarginal.marginalLeft.matrix basis basis else 0).re := by
  rw [ExecutionState.mapClassical_block_mass_diagonalSum]
  apply congrArg Complex.re
  rw [readoutCode, Circuit.measurementSequence_diagonalSum]
  calc
    _ = ExecutionState.diagonalSum state (fun _ basis =>
        if observedBasisVector P count (basisEquiv P count basis.1) = outcome
          then 1 else 0) := by
      apply congrArg (ExecutionState.diagonalSum state)
      funext value basis
      change
        (if observedVector P count
            ((terminalStore P count value.1 basis.1).read (samplesInput P count)) = outcome
          then 1 else 0) = _
      rw [observedVector_after_measurement]
    _ = ∑ basis : (post P count).register.Index,
        (if observedBasisVector P count (basisEquiv P count basis) = outcome
          then (1 : Complex) else 0) *
            state.quantumMarginal.marginalLeft.matrix basis basis :=
      ExecutionState.diagonalSum_localMarginal state (fun basis =>
        if observedBasisVector P count (basisEquiv P count basis) = outcome then 1 else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro basis _
      split <;> simp only [one_mul, zero_mul]

private lemma pure_diagonal_re {R : Register} (state : NormalizedVector R)
    (basis : R.Index) :
    ((DensityOperator.ofPure state).matrix basis basis).re = ‖state basis‖ ^ 2 := by
  rw [DensityOperator.ofPure_matrix]
  exact (congrArg Complex.re (Complex.mul_conj (state basis))).trans
    (Complex.normSq_eq_norm_sq (state basis))

private lemma physicalIndependentState_mass_eq
    (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (basis : (layout P count).Basis) :
    ENNReal.ofReal (‖physicalIndependentState P count expansion basis‖ ^ 2) =
      physicalBasisPMF P count expansion basis := by
  rw [physicalIndependentState_apply, Complex.norm_prod]
  rw [← Finset.prod_pow]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => sq_nonneg _)]
  exact (physicalBasisPMF_apply P count expansion basis).symm

/-- Every output block of the complete actual batch circuit has the independent
physical product-state Born mass. -/
public lemma code_block_mass (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State OrderExecution.pre Reference
      ((OrderExecution.model P).HiddenState × H))
    (normalized : state.IsNormalized)
    (outcome : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count) :
    (((code P count expansion).execute
      (OrderExecution.sourceEnvironment P) Reference state).mapClassical
      (fun value => observedVector P count
        (value.1.read (samplesInput P count))) |>.block outcome).mass =
      ∑ basis : (layout P count).Basis,
        if observedBasisVector P count basis = outcome then
          ‖physicalIndependentState P count expansion basis‖ ^ 2 else 0 := by
  calc
    _ = (∑ basis : (post P count).register.Index,
        if observedBasisVector P count (basisEquiv P count basis) = outcome then
          ((((beforeMeasurement P count expansion).execute
            (OrderExecution.sourceEnvironment P) Reference state).quantumMarginal
            ).marginalLeft).matrix basis basis else 0).re := by
      rw [code, Circuit.execute_seq]
      simpa only [State.mapHistory,
        ExecutionState.executionState_mapClassical_comp, Function.comp_def] using
          readoutCode_block_mass P count
            ((beforeMeasurement P count expansion).execute
              (OrderExecution.sourceEnvironment P) Reference state) outcome
    _ = (∑ basis : (layout P count).Basis,
        if observedBasisVector P count basis = outcome then
          (DensityOperator.ofPure (physicalIndependentState P count expansion)).matrix
            basis basis else 0).re := by
      rw [beforeMeasurement_localDensity P count expansion state normalized]
      apply congrArg Complex.re
      simp only [DensityOperator.reindex_entry, Equiv.symm_symm]
      exact (basisEquiv P count).sum_comp (fun basis : (layout P count).Basis =>
        if observedBasisVector P count basis = outcome then
          (DensityOperator.ofPure (physicalIndependentState P count expansion)).matrix
            basis basis else 0)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted : observedBasisVector P count basis = outcome
      · simp only [accepted, if_true, pure_diagonal_re]
      · simp only [accepted, if_false, Complex.zero_re]

/-- The output of the complete actual batch run is the independent replicated
one-cycle Born law. -/
public lemma run_outputDistribution (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    ((run P count expansion).outputDistribution (OrderExecution.sourceEnvironment P) input).map
        (observedVector P count) =
      PMF.independentReplicateVector (OrderBornBridge.outcomePMF P expansion) count := by
  apply PMF.ext
  intro outcome
  have actual := congrArg
    (fun distribution : PMF (List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count) =>
        distribution outcome)
    (ExecutionState.toPMF_mapClassical ((run P count expansion).execute
      (OrderExecution.sourceEnvironment P) Reference input.state)
      ((run P count expansion).execute_normalized (OrderExecution.sourceEnvironment P) input)
      (fun record => observedVector P count ((run P count expansion).result record)))
  rw [AlgorithmRun.outputDistribution, AlgorithmRun.executionDistribution, PMF.map_comp]
  refine actual.symm.trans ?_
  rw [ExecutionState.toPMF_apply]
  change ENNReal.ofReal
    ((((code P count expansion).execute (OrderExecution.sourceEnvironment P) Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).mapClassical
        (fun value => observedVector P count
          (value.1.read (samplesInput P count))) |>.block outcome).mass) = _
  rw [code_block_mass P count expansion _
    (input.state.mapClassical_normalized input.normalized _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun basis _ => by
    split
    · exact sq_nonneg _
    · exact le_rfl)]
  calc
    _ = ∑ basis : (layout P count).Basis,
        if observedBasisVector P count basis = outcome then
          physicalBasisPMF P count expansion basis else 0 := by
      apply Finset.sum_congr rfl
      intro basis _
      by_cases accepted : observedBasisVector P count basis = outcome
      · simp only [accepted, if_true]
        exact physicalIndependentState_mass_eq P count expansion basis
      · simp only [accepted, if_false, ENNReal.ofReal_zero]
    _ = (physicalBasisPMF P count expansion).map
        (observedBasisVector P count) outcome := by
      rw [PMF.map_apply, tsum_fintype]
      apply Finset.sum_congr rfl
      intro basis _
      by_cases same : outcome = observedBasisVector P count basis
      · rw [if_pos same, if_pos same.symm]
      · rw [if_neg same, if_neg (Ne.symm same)]
    _ = _ := congrArg
      (fun distribution : PMF (List.Vector
        (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count) =>
          distribution outcome)
      (physicalBasisPMF_map_observedBasisVector P count expansion)

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch
