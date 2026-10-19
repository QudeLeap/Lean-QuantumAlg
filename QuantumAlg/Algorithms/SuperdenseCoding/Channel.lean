/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Readout
import all QuantumAlg.Algorithms.SuperdenseCoding.Readout
import all QuantumAlg.Algorithms.SuperdenseCoding.Matrix
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.State.Pure
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Base.State.Density

/-!
# Complete actual superdense-coding channel

A real stored message selects the source encoding and decoding. The joint
state then has one decoded local basis label, so the actual Z instructions
write deterministic outcomes without changing any external-reference entry.
The admission facts are local classical support and the supplied Bell
resource; no restriction on the external reference is introduced
[dW19, qcnotes.tex:879-890,5394,5409].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution
open scoped ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

/-- Actual branch instruction before its measured outputs are read. -/
def selected (count : Nat) : Circuit model (context count) (context count) false :=
  .branch (messageInput count) fun value => .unitary (selectedWord count value)

/-- Only nonzero actual input blocks constrain the real classical input cell. -/
public def messageSupported (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) : Prop :=
  ∀ entry, (state.block entry).mass ≠ 0 →
    entry.1.read (messageInput count) = messageValue bits

/-- Local admitted message support makes every live branch use the same independent operator. -/
lemma selected_quantumMarginal
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (supported : messageSupported count bits state) :
    (((selected count).execute environment) Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (physicalOperator count bits) (1 : UnitaryOperator Reference))
        state.quantumMarginal := by
  rw [selected, Circuit.selectedUnitary_quantumMarginal]
  have same :
      state.applyUnitary (fun entry => UnitaryOperator.prodTensor
        ((selectedWord count (entry.1.read (messageInput count))).matrix environment.quantum)
        (1 : UnitaryOperator Reference)) =
      state.applyUnitary (fun _ => UnitaryOperator.prodTensor
        (physicalOperator count bits) (1 : UnitaryOperator Reference)) := by
    apply ExecutionState.ext
    intro entry
    by_cases absent : (state.block entry).mass = 0
    · apply DensityOperator.ext
      rw [ExecutionState.applyUnitary_block, ExecutionState.applyUnitary_block,
        DensityOperator.eq_zero_of_mass_eq_zero _ absent]
      simp only [DensityOperator.applyUnitary_matrix, DensityOperator.zero_matrix,
        Matrix.mul_zero, Matrix.zero_mul]
    · rw [ExecutionState.applyUnitary_block, ExecutionState.applyUnitary_block,
        supported entry absent, selectedWord, storedBits_messageValue, superdense_placed_matrix]
  rw [same, ExecutionState.fixedUnitary_quantumMarginal]

/-- The complete admitted Bell bank becomes the exact decoded pure local basis. -/
lemma selected_localState
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (supported : messageSupported count bits state)
    (initial : state.quantumMarginal.marginalLeft = DensityOperator.ofPure (initialState count)) :
    (((selected count).execute environment) Reference state).quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket (finalBasis count bits)) := by
  rw [selected_quantumMarginal environment count bits state supported,
    DensityOperator.localUnitary_marginalLeft, initial, ← DensityOperator.ofPure_apply]
  congr 1
  apply NormalizedVector.ext
  intro basis
  exact congrArg (fun vector : HilbertVector (context count).register => vector basis)
    (superdense_physical_correct count bits)

private lemma supported_row_zero {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (seed : ctx.register.Index)
    (pure : state.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket seed))
    (entry : Store ctx × History) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) (different : left ≠ seed) :
    (state.block entry).matrix (left, leftRef) (right, rightRef) = 0 := by
  have promise : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      state.quantumMarginal.marginalLeft := by
    rw [pure]
    change (DensityOperator.ofPure _).matrix = (DensityOperator.ofPure _).mass • _
    rw [DensityOperator.ofPure_normalized]
    simp only [one_smul]
  have block := ExecutionState.block_pureKet_of_localMarginal state seed promise entry
  have diagonal : (state.block entry).marginalLeft.matrix left left = 0 := by
    change (state.block entry).marginalLeft.matrix =
      (state.block entry).marginalLeft.mass •
        (DensityOperator.ofPure (NormalizedVector.ket seed)).matrix at block
    rw [block, Matrix.smul_apply, DensityOperator.ofPure_matrix]
    simp only [NormalizedVector.ket_apply, if_neg different, zero_mul, smul_zero]
  exact DensityOperator.joint_row_zero_of_marginal_diagonal_zero
    (state.block entry) left diagonal leftRef (right, rightRef)

private lemma supported_column_zero {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (seed : ctx.register.Index)
    (pure : state.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket seed))
    (entry : Store ctx × History) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) (different : right ≠ seed) :
    (state.block entry).matrix (left, leftRef) (right, rightRef) = 0 := by
  rw [← (state.block entry).positive.isHermitian.apply (left, leftRef) (right, rightRef),
    supported_row_zero state seed pure entry right left rightRef leftRef different, star_zero]

private lemma labels_self {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) (basis : ctx.register.Index) :
    Circuit.measurementLabelsAgree readouts basis basis := by
  induction readouts with
  | nil => trivial
  | cons head tail ih => exact ⟨rfl, ih⟩

/-- Deterministic basis readout keeps the complete original local-reference matrix. -/
lemma measurement_quantumMarginal
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (pure : state.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket (finalBasis count bits))) :
    (((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count)).execute environment) Reference state).quantumMarginal =
        state.quantumMarginal := by
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  have measured := Circuit.measurementSequence_weightedMatrixEntry
    (allowAllocation := false) (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty)
    (readouts count) environment state (fun _ => (1 : ℂ)) left right leftRef rightRef
  have entryEquation :
      (((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count)).execute environment) Reference state).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
        if Circuit.measurementLabelsAgree (readouts count) left right then
          state.quantumMarginal.matrix (left, leftRef) (right, rightRef) else 0 := by
    simpa only [ExecutionState.weightedMatrixEntry, one_mul,
      ExecutionState.quantumMarginal, Matrix.sum_apply] using measured
  rw [entryEquation]
  by_cases same : Circuit.measurementLabelsAgree (readouts count) left right
  · rw [if_pos same]
  · rw [if_neg same]
    symm
    change (∑ entry, (state.block entry).matrix) (left, leftRef) (right, rightRef) = 0
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro entry _
    by_cases leftSeed : left = finalBasis count bits
    · have rightDifferent : right ≠ finalBasis count bits := by
        intro rightSeed
        exact same (leftSeed ▸ rightSeed ▸ labels_self (readouts count) (finalBasis count bits))
      exact supported_column_zero state _ pure entry left right leftRef rightRef rightDifferent
    · exact supported_row_zero state _ pure entry left right leftRef rightRef leftSeed

/-- Incorrect outputs have zero complete quantum-reference block after the actual writes. -/
lemma superdense_measurement_wrong_output_zero (environment : model.Environment)
    (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (pure : state.quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket (finalBasis count bits))) :
    (ExecutionState.filterClassical
      (((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts count)).execute environment) Reference state)
      (fun entry => entry.1.read (resultInput count) ≠ messageValue bits)).quantumMarginal =
        DensityOperator.zero _ := by
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  rw [ExecutionState.filterClassical_matrix_weighted,
    Circuit.measurementSequence_weightedMatrixEntry, DensityOperator.zero_matrix, Matrix.zero_apply]
  split
  · unfold ExecutionState.weightedMatrixEntry
    apply Finset.sum_eq_zero
    intro entry _
    by_cases same : left = finalBasis count bits
    · subst left
      change (if (Circuit.writeMeasurementPath (readouts count) entry.1
        (Circuit.measurementBasisPath (readouts count) (finalBasis count bits))).read
          (resultInput count) ≠ messageValue bits then (1 : ℂ) else 0) * _ = 0
      rw [superdense_written_output]
      simp only [ne_eq, not_true_eq_false, if_false, zero_mul]
    · rw [supported_row_zero state _ pure entry left right leftRef rightRef same, mul_zero]
  · rfl

/-- Encoding, decoding and real Z readout preserve the entire independently prescribed channel. -/
public lemma superdense_complete_channel
    (environment : model.Environment) (count : Nat) (bits : SuperdenseMessage count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context count) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (supported : messageSupported count bits state)
    (initial : state.quantumMarginal.marginalLeft = DensityOperator.ofPure (initialState count)) :
    (((code count).execute environment) Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (physicalOperator count bits) (1 : UnitaryOperator Reference))
        state.quantumMarginal := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  change (((Circuit.measurementSequence (allowAllocation := false)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty)
        (readouts count)).execute environment) Reference
      (((selected count).execute environment) Reference state)).quantumMarginal = _
  rw [measurement_quantumMarginal environment count bits _
      (selected_localState environment count bits state supported initial),
    selected_quantumMarginal environment count bits state supported]

end
end QuantumAlg.SuperdenseCoding.Execution
