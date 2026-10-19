/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Density
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Readout
public import QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Density
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Readout
import all QuantumAlg.Primitives.ZReset.Bank.OperationModel
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Core.Execution.Interpret

/-!
# Complete reference observations of one reused binary DLP sample

The trailing physical reset preserves every retained sample jointly with the
external reference. On the real zero seed, the preceding native word and
measurement supply the binary Born weight in every complete original store.
No independence of the incoming store, service state or reference is assumed
[Sho95, source.tex:1784-1984] [dW19, qcnotes.tex:5409-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma indicator_reference {C D : Type} [Fintype C]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (read : C → D) (value : D) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state
      (fun entry _ => if read entry = value then 1 else 0) leftRef rightRef =
      ∑ basis : R.Index,
        (state.filterClassical (fun entry => read entry = value)).quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef) := by
  simp only [ExecutionState.referenceFiberSum, ExecutionState.quantumMarginal,
    Matrix.sum_apply, ExecutionState.filterClassical_block, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix, Matrix.ite_apply, Matrix.zero_apply,
    ite_mul, one_mul, zero_mul]

/-- The real bank reset preserves arbitrary complex weights on all retained samples. -/
public lemma reset_samples_reference (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (weight : (CShape.fixedVector count
      (.fixedVector (sampleWidth P) (.finite 2))).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((reset P count).execute (sourceEnvironment P) Reference state)
      (fun entry _ => weight (entry.1.read (samplesInput P count))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (samplesInput P count))) leftRef rightRef := by
  rw [← ExecutionState.referenceFiberSum_observation_fibers
    ((reset P count).execute (sourceEnvironment P) Reference state)
    (fun entry _ => entry.1.read (samplesInput P count)) weight]
  rw [← ExecutionState.referenceFiberSum_observation_fibers state
    (fun entry _ => entry.1.read (samplesInput P count)) weight]
  apply Finset.sum_congr rfl
  intro value _
  apply congrArg (fun coefficient : ℂ => weight value * coefficient)
  rw [indicator_reference, indicator_reference]
  have entries (basis : (context P count).register.Index) :=
    ZReset.Bank.zResetBank_complete_read_entry_operationModel
      (environment := ⟨Binary.Oracle.interpretation P,
      ClassicalFiniteGroupOracle.interpretation G⟩) (allowAllocation := true)
      (oracles := Binary.Oracle.model P)
      (services := ClassicalFiniteGroupOracle.model G)
      (qubits P count) (scratch P count) BitWord.model state
      (samplesInput P count) (scratch_separate_samples P count) value
      basis basis leftRef rightRef
  have single (coefficient : ℂ) :
      (∑ basis : (context P count).register.Index,
        if basis = (context P count).quantumLayout.zeroLabel ∧
          basis = (context P count).quantumLayout.zeroLabel then coefficient else 0) =
        coefficient := by
    simp only [and_self, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact (Finset.sum_congr rfl (fun basis _ => entries basis)).trans (single _)

/-- The actual native word acts on the zero column of every stored reference block. -/
private lemma nativeProgram_seed_entry (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (seeded : BasisSeeded.Holds (context P count).quantumLayout.zeroLabel state)
    (original : Store (context P count)) (left right : (context P count).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((QuantumAlg.Circuit.unitary (allowAllocation := true)
      (nativeProgram P count expansion)).execute (sourceEnvironment P) Reference
      state).filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      runtimeSourceState P count expansion left *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((context P count).quantumLayout.zeroLabel, leftRef)
          ((context P count).quantumLayout.zeroLabel, rightRef) *
        star (runtimeSourceState P count expansion right) := by
  have filtered := QuantumAlg.Circuit.unitary_store_filter
    (environment := sourceEnvironment P) (allowAllocation := true)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (services := ClassicalFiniteGroupOracle.model G)
    (ctx := context P count)
    (nativeProgram P count expansion) state (fun store => store = original)
  refine (congrArg (fun density : DensityOperator
      (Register.prod (context P count).register Reference) =>
        density.matrix (left, leftRef) (right, rightRef)) filtered).trans ?_
  refine (BasisSeeded.unitary_entry (ctx := context P count)
    (context P count).quantumLayout.zeroLabel state seeded
    ((nativeProgram P count expansion).matrix
      (Binary.Oracle.interpretation P)) original left right leftRef rightRef).trans ?_
  exact congrArg₂ (fun leftAmplitude rightAmplitude : ℂ => leftAmplitude *
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((context P count).quantumLayout.zeroLabel, leftRef)
      ((context P count).quantumLayout.zeroLabel, rightRef) * star rightAmplitude)
    (reusableDLP_nativeProgram_zero_amplitude P count expansion left)
    (reusableDLP_nativeProgram_zero_amplitude P count expansion right)

/-- The trailing reset leaves the actual measurement's retained-sample reference law intact. -/
public lemma round_samples_reference (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (weight : (CShape.fixedVector count
      (.fixedVector (sampleWidth P) (.finite 2))).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((round P slot expansion).execute
      (sourceEnvironment P) Reference state)
      (fun entry _ => weight (entry.1.read (samplesInput P count))) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((QuantumAlg.Circuit.unitary (allowAllocation := true)
          (nativeProgram P count expansion)).execute (sourceEnvironment P) Reference state)
        (fun entry basis => weight
          ((measuredStore P slot entry.1 basis).read (samplesInput P count)))
        leftRef rightRef := by
  let native : QuantumAlg.Circuit (model P) (context P count) (context P count) :=
    .unitary (nativeProgram P count expansion)
  let measure : QuantumAlg.Circuit (model P) (context P count) (context P count) :=
    .measurementSequence (readouts P slot)
  have first := QuantumAlg.Circuit.referenceFiberSum_execute_seq
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    native (measure.seq (reset P count)) state
    (fun store => weight (store.read (samplesInput P count))) leftRef rightRef
  have second := QuantumAlg.Circuit.referenceFiberSum_execute_seq
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    measure (reset P count) (native.execute (sourceEnvironment P) Reference state)
    (fun store => weight (store.read (samplesInput P count))) leftRef rightRef
  refine first.trans (second.trans ((reset_samples_reference P count
    (measure.execute
      (sourceEnvironment P) Reference (native.execute
        (sourceEnvironment P) Reference state)) weight leftRef rightRef).trans ?_))
  exact QuantumAlg.Circuit.measurementSequence_referenceFiberSum
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (classicalOracles := ClassicalFiniteGroupOracle.model G)
    (ctx := context P count)
    (readouts P slot) (native.execute (sourceEnvironment P) Reference state)
    (fun entry _ => weight (entry.1.read (samplesInput P count))) leftRef rightRef

private lemma source_weight (amplitude coefficient : ℂ) :
    amplitude * coefficient * star amplitude =
      ((‖amplitude‖ ^ 2 : ℝ) : ℂ) * coefficient := by
  calc
    _ = (amplitude * star amplitude) * coefficient := by ring
    _ = _ := congrArg (fun value : ℂ => value * coefficient)
      (by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude)

omit [Fintype G] in
private lemma runtime_probability (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (outcome : TerminalZMeasure.Outcome (sampleWidth P)) :
    (∑ basis : (context P count).register.Index,
      if Binary.readout P (basisEquiv P count basis) = outcome then
        ‖runtimeSourceState P count expansion basis‖ ^ 2 else 0) =
      (Binary.outcomePMF P expansion outcome).toReal := by
  have reindex := (basisEquiv P count).sum_comp (fun basis =>
    if Binary.readout P basis = outcome then
      ‖Binary.Fourier.evolvedState P expansion basis‖ ^ 2 else 0)
  refine reindex.trans ?_
  rw [Binary.outcomePMF, Binary.basisPMF, PMF.map_ofFintype, PMF.ofFintype_apply]
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro basis _
  by_cases same : Binary.readout P basis = outcome
  · simp only [same, if_true, ENNReal.toReal_ofReal (sq_nonneg _)]
  · simp only [same, if_false]

/-- A fresh sample has its source Born weight jointly with any retained stable sample weight. -/
private lemma round_outcome_weighted_reference (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    (weight : (CShape.fixedVector count
      (.fixedVector (sampleWidth P) (.finite 2))).Value → ℂ)
    (stable : ∀ store basis,
      weight ((measuredStore P slot store basis).read (samplesInput P count)) =
        weight (store.read (samplesInput P count)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (seeded : BasisSeeded.Holds (context P count).quantumLayout.zeroLabel state)
    (outcome : TerminalZMeasure.Outcome (sampleWidth P)) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((round P slot expansion).execute
      (sourceEnvironment P) Reference state)
      (fun entry _ => weight (entry.1.read (samplesInput P count)) *
        (if observedOutcome P (entry.1.read (sampleInput P slot)) = outcome then 1 else 0))
      leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (samplesInput P count)) *
          ((Binary.outcomePMF P expansion outcome).toReal : ℂ)) leftRef rightRef := by
  have measured := round_samples_reference P slot expansion state
    (fun values => weight values *
      (if observedOutcome P (values.get slot) = outcome then 1 else 0)) leftRef rightRef
  refine measured.trans ?_
  simp only [samplesInput_get, stable, observed_after_measurement]
  have blocks := BasisSeeded.fiber_store_blocks (ctx := context P count) (Reference := Reference)
    ((QuantumAlg.Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := ClassicalFiniteGroupOracle.model G)
      (nativeProgram P count expansion)).execute (sourceEnvironment P) Reference state)
    (fun original basis => weight (original.read (samplesInput P count)) *
      (if Binary.readout P (basisEquiv P count basis) = outcome then 1 else 0))
    leftRef rightRef
  have seed := BasisSeeded.referenceFiberSum_seed (ctx := context P count)
    (context P count).quantumLayout.zeroLabel state seeded
    (fun original => weight (original.read (samplesInput P count)) *
      ((Binary.outcomePMF P expansion outcome).toReal : ℂ)) leftRef rightRef
  refine blocks.trans (Eq.trans ?_ seed.symm)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  simp only [nativeProgram_seed_entry P count expansion state seeded, source_weight]
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((context P count).quantumLayout.zeroLabel, leftRef)
      ((context P count).quantumLayout.zeroLabel, rightRef)
  have terms : ∀ basis : (context P count).register.Index,
      (weight (original.read (samplesInput P count)) *
        (if Binary.readout P (basisEquiv P count basis) = outcome then (1 : ℂ) else 0)) *
          (((‖runtimeSourceState P count expansion basis‖ ^ 2 : ℝ) : ℂ) * coefficient) =
      weight (original.read (samplesInput P count)) *
        (((if Binary.readout P (basisEquiv P count basis) = outcome then
          ‖runtimeSourceState P count expansion basis‖ ^ 2 else 0 : ℝ) : ℂ) * coefficient) := by
    intro basis
    by_cases same : Binary.readout P (basisEquiv P count basis) = outcome <;> simp [same]
  change (∑ basis : (context P count).register.Index,
      (weight (original.read (samplesInput P count)) *
        (if Binary.readout P (basisEquiv P count basis) = outcome then (1 : ℂ) else 0)) *
        (((‖runtimeSourceState P count expansion basis‖ ^ 2 : ℝ) : ℂ) * coefficient)) =
    (weight (original.read (samplesInput P count)) *
      ((Binary.outcomePMF P expansion outcome).toReal : ℂ)) * coefficient
  simp only [terms, ← Finset.mul_sum, ← Finset.sum_mul, ← Complex.ofReal_sum,
    runtime_probability]
  ring

/-- The new outcome has the same complete reference law for every admitted local zero state. -/
public lemma round_outcome_reference (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (pure : (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds state.quantumMarginal.marginalLeft)
    (outcome : TerminalZMeasure.Outcome (sampleWidth P)) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((round P slot expansion).execute
      (sourceEnvironment P) Reference state)
      (fun entry _ => if observedOutcome P (entry.1.read (sampleInput P slot)) = outcome
        then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ((Binary.outcomePMF P expansion outcome).toReal : ℂ)) leftRef rightRef := by
  simpa only [one_mul] using round_outcome_weighted_reference P slot expansion
    (fun _ => 1) (by intro _ _; rfl) state (seeded_of_pure _ _ pure)
    outcome leftRef rightRef

/-- The actual retained sample has the binary PMF under precisely the local zero promise. -/
public lemma round_toPMF (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (normalized : state.IsNormalized)
    (pure : (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds state.quantumMarginal.marginalLeft) :
    ((((round P slot expansion).execute (sourceEnvironment P) Reference state).toPMF
      (by exact (QuantumAlg.Circuit.execute_mass
        (environment := sourceEnvironment P)
        (round P slot expansion) Reference state).trans normalized)).map
      (fun entry => observedOutcome P (entry.1.read (sampleInput P slot)))) =
      Binary.outcomePMF P expansion := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
  exact round_outcome_reference P slot expansion state pure

end

end QuantumAlg.FiniteCyclicDLP.Reusable
