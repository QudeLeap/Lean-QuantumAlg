/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Probability
public import QuantumAlg.Core.Execution.Basis.Seeded
public import QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Fourier
import all QuantumAlg.Primitives.ZReset.Bank.Local
import all QuantumAlg.Core.Execution.State.Pure
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Basis.Seeded.Admission
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Actual single-bank state before and after each finite-cyclic sample

The terminal reset supplies zero support separately in every complete stored
block. Consequently the next real native word starts at zero without another
reset or preparation. These statements keep arbitrary probability mass and
external-reference correlations [dW19, qcnotes.tex:5381-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G]

/-- The proven binary source vector on this same physical runtime bank. -/
public def runtimeSourceState (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) : NormalizedVector (context P count).register :=
  NormalizedVector.reindex (basisEquiv P count).symm
    (Binary.Fourier.evolvedState P expansion)

/-- Equal-wire placement gives the exact native binary matrix entry. -/
public lemma reusableDLP_nativeProgram_matrix_entry (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (row column : (context P count).register.Index) :
    ((nativeProgram P count expansion).matrix (Binary.Oracle.interpretation P)) row column =
      ((Binary.Circuit.circuit P expansion).matrix (Binary.Oracle.interpretation P))
        (basisEquiv P count row) (basisEquiv P count column) := by
  unfold nativeProgram basisEquiv
  rw [Execution.unitaryOfEqualWires_matrix]
  rfl

/-- The actual runtime zero column is the phase-exact binary output vector. -/
public lemma reusableDLP_nativeProgram_zero_amplitude (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (row : (context P count).register.Index) :
    ((nativeProgram P count expansion).matrix
      (Binary.Oracle.interpretation P)) row (context P count).quantumLayout.zeroLabel =
      runtimeSourceState P count expansion row := by
  rw [reusableDLP_nativeProgram_matrix_entry, reusableDLP_basisEquiv_zero]
  change ((Binary.Circuit.circuit P expansion).matrix
    (Binary.Oracle.interpretation P)) (basisEquiv P count row)
      (Binary.Oracle.layout P).zeroLabel =
    ((Binary.Circuit.circuit P expansion).matrix (Binary.Oracle.interpretation P)).applyVec
      (NormalizedVector.ket (R := (Binary.Oracle.layout P).register)
        (Binary.Oracle.layout P).zeroLabel) (basisEquiv P count row)
  exact (HilbertOperator.applyVec_ket
    (((Binary.Circuit.circuit P expansion).matrix (Binary.Oracle.interpretation P)) :
      HilbertOperator (Binary.Oracle.layout P).register)
    (Binary.Oracle.layout P).zeroLabel (basisEquiv P count row)).symm

/-- The same literal runtime word acts on the physically prepared zero state. -/
public lemma nativeProgram_apply_zero (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ((nativeProgram P count expansion).matrix (Binary.Oracle.interpretation P)).apply
      (NormalizedVector.ket (R := (context P count).register)
        (context P count).quantumLayout.zeroLabel) = runtimeSourceState P count expansion := by
  apply NormalizedVector.ext
  intro row
  change ((nativeProgram P count expansion).matrix (Binary.Oracle.interpretation P)).applyVec
    (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel : HilbertVector (context P count).register)
    row = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    reusableDLP_nativeProgram_zero_amplitude]

variable [Fintype G]

/-- The real terminal reset returns zero at the input's actual mass, including mass zero. -/
public lemma reset_pure (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History)) :
    (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds
        ((reset P count).execute
          (sourceEnvironment P) Reference state).quantumMarginal.marginalLeft :=
  ZReset.Bank.zResetBank_localDensity_pure
    (environment := ⟨Binary.Oracle.interpretation P,
      ClassicalFiniteGroupOracle.interpretation G⟩)
    (services := ClassicalFiniteGroupOracle.model G)
    (qubits P count) (scratch P count) BitWord.model state

private lemma seeded_of_pure {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (seed : ctx.register.Index)
    (pure : (StatePromise.pure (NormalizedVector.ket seed)).Holds
      state.quantumMarginal.marginalLeft) : BasisSeeded.Holds seed state := by
  apply BasisSeeded.of_block_marginal_support seed state
  intro entry basis different
  have block := ExecutionState.block_pureKet_of_localMarginal state seed pure entry
  change (state.block entry).marginalLeft.matrix =
    (state.block entry).marginalLeft.mass • (DensityOperator.ofPure
      (NormalizedVector.ket seed)).matrix at block
  rw [block, Matrix.smul_apply, DensityOperator.ofPure_matrix]
  simp only [NormalizedVector.ket_apply, if_neg different, zero_mul, smul_zero]

/-- Reset establishes the next seed in every complete actual store-reference block. -/
private lemma reusableDLP_reset_seeded (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History)) :
    BasisSeeded.Holds (context P count).quantumLayout.zeroLabel
      ((reset P count).execute (sourceEnvironment P) Reference state) :=
  seeded_of_pure _ _ (reset_pure P count state)

/-- A seeded round's actual unitary gives the binary source density at unchanged mass. -/
public lemma beforeReadout_matrix (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (pure : (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds state.quantumMarginal.marginalLeft) :
    ((QuantumAlg.Circuit.unitary (allowAllocation := true)
      (nativeProgram P count expansion)).execute (sourceEnvironment P) Reference
      state).quantumMarginal.marginalLeft.matrix =
      state.mass • (DensityOperator.ofPure (runtimeSourceState P count expansion)).matrix := by
  change state.quantumMarginal.marginalLeft.matrix =
    state.quantumMarginal.marginalLeft.mass • _ at pure
  rw [DensityOperator.marginalLeft_mass, ExecutionState.quantumMarginal_mass] at pure
  rw [QuantumAlg.Circuit.unitary_localDensity, DensityOperator.applyUnitary_matrix,
    pure, Matrix.mul_smul, Matrix.smul_mul]
  change state.mass • (DensityOperator.applyUnitary
    ((nativeProgram P count expansion).matrix
      (Binary.Oracle.interpretation P)) (DensityOperator.ofPure
      (NormalizedVector.ket (R := (context P count).register)
        (context P count).quantumLayout.zeroLabel))).matrix = _
  rw [← DensityOperator.ofPure_apply, nativeProgram_apply_zero]

/-- Every complete round, including the final round, leaves the single bank at zero. -/
public lemma round_pure (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History)) :
    (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds
        ((round P slot expansion).execute
          (sourceEnvironment P) Reference state).quantumMarginal.marginalLeft := by
  unfold round
  rw [QuantumAlg.Circuit.execute_seq, State.mapHistory_quantumMarginal,
    QuantumAlg.Circuit.execute_seq, State.mapHistory_quantumMarginal]
  exact reset_pure P count _

/-- Full stored-block support after each real round justifies allocation-free sequential reuse. -/
private lemma round_seeded (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History)) :
    BasisSeeded.Holds (context P count).quantumLayout.zeroLabel
      ((round P slot expansion).execute (sourceEnvironment P) Reference state) :=
  seeded_of_pure _ _ (round_pure P slot expansion state)

end

end QuantumAlg.FiniteCyclicDLP.Reusable
