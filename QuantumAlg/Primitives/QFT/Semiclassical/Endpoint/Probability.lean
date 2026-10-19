/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.State
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Base.State.Density
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Fourier Born probabilities of the actual retained result vector

The actual output PMF is observed through the mathematical frequency
equivalence of its n existing cells. The full mixed-state instrument gives
the usual Born formula when its actual local input density is pure. The
normalized vector supplies the amplitudes; no prescribed sampler or output
distribution is an assumption. The result covers n at least one and also
the zero-width boundary [GN96, 9511007.tex:100-114,246-266].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

open Execution MeasurementInstrument
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The output probability is the mass of the block read from the run's actual final store. -/
lemma algorithm_output_probability {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat) {Reference :
    Register}
    (input : OracleInput .empty (inputContext n) Reference)
    (value : CShape.Value (.fixedVector n (.finite 2))) :
    ((algorithm inverse n).outputDistribution environment) input value =
      ENNReal.ofReal (((((algorithm inverse n).run.finalState environment) Reference
        input.state).mapClassical
        (resultRead n).eval).block value).mass := by
  unfold Algorithm.outputDistribution AlgorithmRun.outputDistribution
    AlgorithmRun.executionDistribution
  let run := (algorithm inverse n).run
  have actual := congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical ((run.execute environment) Reference input.state)
      ((run.execute_normalized environment) input) run.result)
  rw [ExecutionState.toPMF_apply] at actual
  refine actual.symm.trans ?_
  apply congrArg ENNReal.ofReal
  congr 2
  unfold AlgorithmRun.finalState
  rw [ExecutionState.executionState_mapClassical_comp]
  rfl

/-- Each actual result vector has precisely its derived ideal Fourier branch density. -/
lemma algorithm_result_density {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat) {Reference :
    Register}
    (input : OracleInput .empty (inputContext n) Reference) (outcome : Bits n) :
    ((((algorithm inverse n).run.finalState environment) Reference input.state).mapClassical
      (resultRead n).eval).block (resultValue n outcome) =
      (ZMeasurement.branch
        (fun basis : (Register.prod (Qubits n) Reference).Index => basis.1) (binaryEquiv n outcome)
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (idealOperator inverse n) (1 : UnitaryOperator Reference))
          (binaryInput n Reference input.caller))).reindex
            (outputJointBasis n Reference).symm := by
  rw [algorithm_finalState]
  have observed :
      ((((body inverse n).execute environment) Reference (allocatedInput
        (environment := environment) n input)).mapClassical
        Prod.fst).mapClassical (resultRead n).eval =
      (((body inverse n).execute environment) Reference (allocatedInput
        (environment := environment) n input)).mapClassical
        (fun entry => (resultRead n).eval entry.1) := by
    refine (ExecutionState.executionState_mapClassical_comp_instances
      (result := inferInstance) _ _ _).trans ?_
    apply ExecutionState.executionState_mapClassical_congr
    rfl
  rw [observed]
  apply DensityOperator.ext
  rw [body_result_matrix, sourceOutcomeKraus_endpoint_conjugation,
    allocatedInput_binary]
  exact congrArg
    (fun matrix : Matrix ((Qubits n).Index × Reference.Index)
        ((Qubits n).Index × Reference.Index) Complex =>
      matrix.submatrix (outputJointBasis n Reference) (outputJointBasis n Reference))
    (bankBranch_eq_measured_unitary (R := Qubits n) (Reference := Reference)
      (idealOperator inverse n) (binaryInput n Reference input.caller) (binaryEquiv n outcome))

private lemma measured_bank_mass {R Reference : Register}
    (state : DensityOperator (R.prod Reference)) (outcome : R.Index) :
    (ZMeasurement.branch (fun basis : (R.prod Reference).Index => basis.1) outcome state).mass =
      (state.marginalLeft.matrix outcome outcome).re := by
  let matrix : Matrix (R.Index × Reference.Index) (R.Index × Reference.Index) Complex :=
    state.matrix
  rw [ZMeasurement.branch_mass]
  change (∑ index : R.Index × Reference.Index,
    if index.1 = outcome then (matrix index index).re else 0) =
      (state.marginalLeft.matrix outcome outcome).re
  rw [DensityOperator.marginalLeft_matrix]
  change (∑ index : R.Index × Reference.Index,
    if index.1 = outcome then (matrix index index).re else 0) =
      (∑ reference : Reference.Index, matrix (outcome, reference) (outcome, reference)).re
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.re_sum]

/-- All outcome masses are the diagonal entries of the independent transformed local input. -/
lemma algorithm_result_probability {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat) {Reference :
    Register}
    (input : OracleInput .empty (inputContext n) Reference) (outcome : Bits n) :
    ((algorithm inverse n).outputDistribution environment) input (resultValue n outcome) =
      ENNReal.ofReal ((DensityOperator.applyUnitary (idealOperator inverse n)
        (binaryInput n Reference input.caller).marginalLeft).matrix
          (binaryEquiv n outcome) (binaryEquiv n outcome)).re := by
  rw [algorithm_output_probability, algorithm_result_density, DensityOperator.reindex_mass,
    measured_bank_mass, DensityOperator.localUnitary_marginalLeft]

/-- The real stored vector of the physical tuple decodes to the canonical Fourier frequency. -/
lemma resultValue_frequency (n : Nat) (frequency : Fin (2 ^ n)) :
    frequencyEquiv n (resultValue n (frequencyBits n frequency)) = frequency := by
  rw [qftSemiclassical_frequencyEquiv_apply]
  unfold Endpoint.frequency
  rw [physicalLabel_resultValue, qftSemiclassical_frequencyBits_physicalLabel,
    qftReverseBits_involutive]

/-- Mapping the real output PMF through its bijective mathematical label changes no probability. -/
lemma algorithm_frequency_probability {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat) {Reference :
    Register}
    (input : OracleInput .empty (inputContext n) Reference) (frequency : Fin (2 ^ n)) :
    (((algorithm inverse n).outputDistribution environment) input).map (frequencyEquiv n) frequency
      =
      ((algorithm inverse n).outputDistribution environment) input
        (resultValue n (frequencyBits n frequency)) := by
  rw [PMF.map_apply]
  have selected (value : CShape.Value (.fixedVector n (.finite 2))) :
      frequency = frequencyEquiv n value ↔
        value = resultValue n (frequencyBits n frequency) := by
    constructor
    · intro same
      apply (frequencyEquiv n).injective
      exact same.symm.trans (resultValue_frequency n frequency).symm
    · intro same
      rw [same, resultValue_frequency]
  simp only [selected, tsum_ite_eq]

private lemma forward_amplitude (n : Nat) (state : NormalizedVector (Qubits n))
    (frequency : Fin (2 ^ n)) :
    (idealOperator false n).apply state (qftReverseBits n frequency) =
      invSqrtN n * ∑ index : Fin (2 ^ n),
        state index * ω n ^ (index.val * frequency.val) := by
  change (idealOperator false n).applyVec (state : HilbertVector (Qubits n))
    (qftReverseBits n frequency) = _
  rw [UnitaryOperator.applyVec_apply]
  simp only [idealOperator_entry, Bool.false_eq_true, if_false, qftReverseBits_involutive,
    QFTOperator_entry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [Nat.mul_comm frequency.val index.val]
  ring

/-- The actual decoded output has the Fourier Born law for every normalized amplitude vector. -/
lemma algorithm_frequency_born {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (n : Nat) {Reference : Register}
    (input : OracleInput .empty (inputContext n) Reference)
    (amplitudes : NormalizedVector (Qubits n))
    (pureInput : (binaryInput n Reference input.caller).marginalLeft =
      DensityOperator.ofPure amplitudes) (frequency : Fin (2 ^ n)) :
    (((algorithm false n).outputDistribution environment) input).map (frequencyEquiv n) frequency =
      ENNReal.ofReal (((2 : Real) ^ n)⁻¹ *
        ‖∑ index : Fin (2 ^ n),
          amplitudes index * ω n ^ (index.val * frequency.val)‖ ^ 2) := by
  rw [algorithm_frequency_probability, algorithm_result_probability, pureInput,
    ← DensityOperator.ofPure_apply, DensityOperator.ofPure_matrix,
    qftSemiclassical_frequencyBits_physicalLabel, forward_amplitude]
  apply congrArg ENNReal.ofReal
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
    norm_mul, mul_pow, norm_sq_invSqrtN]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
