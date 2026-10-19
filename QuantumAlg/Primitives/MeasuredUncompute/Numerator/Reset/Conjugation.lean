/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Projection
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Fibers

/-!
# Exact full-state matrix of the actual H/Z/stored-X sequence

The actual final store determines both its original classical fibers and
the native X sequence that is executed. This equality factors that same
interpreter result into its existing Hadamard, Z projection, and selected
reset matrices, retaining every external-reference entry and every prefix
coordinate [LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorResetConjugation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma source_hadamard (width : Nat) {Reference : Register} {History : Type}
    [Fintype History] (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context width)) :
    NumeratorStoredProjection.source width
      ((NumeratorReset.hadamard width).execute environment Reference state) stored =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
            environment.quantum)
          (1 : UnitaryOperator Reference))
        (NumeratorStoredProjection.source width state stored) :=
  Circuit.unitary_store_filter
    (NumeratorRuntime.program width (NumeratorReset.hadamardMember width))
    environment state
    (fun original => Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) original
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width)
        (NumeratorStoredProjection.representative width
          (NumeratorReset.outcome (stored.read (input width))))) = stored)

/-- The actual H/Z/reset state keeps exactly its selected source fiber and complete reference. -/
lemma actual_density (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical ((NumeratorReset.code width).execute environment Reference
      state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          ((NumeratorRuntime.program width
            (NumeratorReset.member width (stored.read (input width)))).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        (ZMeasurement.branch
          (fun entry : (Register.prod (context width).register Reference).Index =>
            word width entry.1)
          (NumeratorReset.outcome (stored.read (input width)))
          (DensityOperator.applyUnitary
            (UnitaryOperator.prodTensor
              ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
                environment.quantum)
              (1 : UnitaryOperator Reference))
            (NumeratorStoredProjection.source width state stored))) := by
  rw [NumeratorReset.code, Circuit.seq_store_marginal]
  have resetDensity := NumeratorResetMatrix.actual_density (runtimeEnvironment := environment) width
    ((NumeratorReset.hadamard width).execute environment Reference state) stored
  dsimp only [NumeratorMeasurement.measure] at resetDensity
  refine resetDensity.trans ?_
  unfold NumeratorResetMatrix.density
  rw [NumeratorStoredProjection.actual_density, source_hadamard]

/-- This matrix product records the same three actual steps for the actual stored word. -/
def operator (interpretation : OracleModel.empty.Interpretation)
    (width : Nat) (Reference : Register) (stored : Store (context width)) :
    HilbertOperator (Register.prod (context width).register Reference) :=
  (UnitaryOperator.prodTensor
      ((NumeratorRuntime.program width
        (NumeratorReset.member width (stored.read (input width)))).matrix interpretation)
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod (context width).register Reference)) *
    ZMeasurement.projector
      (fun entry : (Register.prod (context width).register Reference).Index =>
            word width entry.1)
      (NumeratorReset.outcome (stored.read (input width))) *
    (UnitaryOperator.prodTensor
      ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix interpretation)
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod (context width).register Reference))

private lemma measured_density (width : Nat) (allowAllocation : Bool) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((Circuit.measurementSequence (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width)).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      ZMeasurement.branch
        (fun entry : ((context width).register.prod Reference).Index => word width entry.1)
        (NumeratorReset.outcome (stored.read (input width))) state.quantumMarginal := by
  classical
  let writes (original : Store (context width)) (basis : (context width).register.Index) :=
    Circuit.writeMeasurementPath (allowAllocation := allowAllocation) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) original
      (Circuit.measurementBasisPath (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width) basis)
  have written_word (original : Store (context width))
      (basis : (context width).register.Index) :
      NumeratorReset.outcome ((writes original basis).read (input width)) = word width basis := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    rw [NumeratorReset.outcome_bit]
    exact (QubitReadouts.written_mask (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (services := .empty)
      (wire width) (wire_dimension width) (cell width) (cells_distinct width)
      original basis index).trans
        ((wire_basis_bit width basis index).trans (word_bit width basis index))
  have writes_iff (original : Store (context width))
      (basis : (context width).register.Index) :
      writes original basis = stored ↔
        word width basis = NumeratorReset.outcome (stored.read (input width)) := by
    constructor
    · intro same
      exact (written_word original basis).symm.trans
        (congrArg (fun result : Store (context width) =>
          NumeratorReset.outcome (result.read (input width))) same)
    · intro same
      exact NumeratorStoredFibers.outcome_injective width
        ((written_word original basis).trans same)
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  rw [Circuit.measurementSequence_store_matrix_entry, ZMeasurement.branch_matrix]
  have weights :
      (fun original : Store (context width) × (ClassicalOracleModel.empty.HiddenState × History) =>
        if Circuit.writeMeasurementPath (allowAllocation := allowAllocation)
          (gates := AlgorithmGate.model)
          (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
          (readouts width) original.1
          (Circuit.measurementBasisPath (allowAllocation := allowAllocation)
            (gates := AlgorithmGate.model)
            (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
            (readouts width) left) = stored then (1 : ℂ) else 0) =
        fun _ => if word width left = NumeratorReset.outcome (stored.read (input width))
          then (1 : ℂ) else 0 := by
    funext original
    exact if_congr (writes_iff original.1 left) rfl rfl
  have constant (value : ℂ) :
      ExecutionState.weightedMatrixEntry state (fun _ => value)
        (left, leftRef) (right, rightRef) =
        value * state.quantumMarginal.matrix (left, leftRef) (right, rightRef) := by
    simp only [ExecutionState.weightedMatrixEntry, ExecutionState.quantumMarginal,
      Matrix.sum_apply, Finset.mul_sum]
  rw [weights, constant]
  have agree := measurement_agrees width left right
  by_cases same : word width left = word width right
  · rw [if_pos (agree.mpr same)]
    by_cases first : word width left = NumeratorReset.outcome (stored.read (input width))
    · rw [if_pos first, if_pos ⟨first, same.symm.trans first⟩, one_mul]
    · rw [if_neg first, if_neg (fun both => first both.1), zero_mul]
  · rw [if_neg (fun actual => same (agree.mp actual)),
      if_neg (fun both => same (both.1.trans both.2.symm))]

/-- Full conjugation is an equality of the actual retained-store block, not a separate execution. -/
lemma actual_matrix (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width))
    (allowAllocation : Bool := true) :
    (ExecutionState.filterClassical
      ((NumeratorReset.code width allowAllocation).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      operator environment.quantum width Reference stored *
        (NumeratorStoredProjection.source width state stored).matrix *
        (operator environment.quantum width Reference stored).conjTranspose := by
  classical
  let hadamard : Circuit (.quantum AlgorithmGate.model .empty)
      (context width) (context width) allowAllocation :=
    .unitary (NumeratorRuntime.program width (NumeratorReset.hadamardMember width))
  let prepared : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × hadamard.Path)) :=
    hadamard.execute environment Reference state
  have measured := measured_density (environment := environment) width allowAllocation prepared
    stored
  have preparedMarginal : prepared.quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
            environment.quantum)
          (1 : UnitaryOperator Reference)) state.quantumMarginal :=
    Circuit.unitary_jointDensity (allowAllocation := allowAllocation)
      (operations := .empty) (services := .empty)
      environment (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)) state
  rw [NumeratorStoredFibers.source_eq_marginal]
  unfold NumeratorReset.code NumeratorReset.hadamard NumeratorReset.reset
    NumeratorRuntime.selected NumeratorRuntime.code
  rw [Circuit.seq_store_marginal, Circuit.seq_store_marginal,
    Circuit.selectedUnitary_store_matrix (allowAllocation := allowAllocation)]
  refine (congrArg (fun density : DensityOperator ((context width).register.prod Reference) =>
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor
        ((NumeratorRuntime.program width
          (NumeratorReset.member width (stored.read (input width)))).matrix environment.quantum)
        (1 : UnitaryOperator Reference)) density).matrix) measured).trans ?_
  rw [preparedMarginal]
  simp only [DensityOperator.applyUnitary_matrix, ZMeasurement.branch,
    NumeratorResetConjugation.operator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.MeasuredUncompute.NumeratorResetConjugation
