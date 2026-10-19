/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Density
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Pure.Selection
import all QuantumAlg.Core.Execution.State.Pure
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Primitives.ZReset.Bank

/-!
# Full-record physical restart after every sequential finite-cyclic sample

Every round, including the last, physically measures and resets the entire
owned binary bank. Its actual complete store, hidden service and path blocks
retain the same predetermined zero label with arbitrary external reference.
These cleanup facts are used only together with independently stated sample
protocols [dW19, qcnotes.tex:5394-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G]

private lemma cells_noBorrowed {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (dimension : ℕ+) (count : Nat) :
    (MeasurementCells.context ctx dimension count).borrowedQuantumWires =
      ctx.borrowedQuantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [MeasurementCells.context, RuntimeCtx.borrowedQuantumWires_addRetained]
        using ih

/-- The one actual quantum bank is entirely owned by this algorithm. -/
private lemma noBorrowedQuantum (P : KnownOrderProblem G) (count : Nat) :
    (context P count).borrowedQuantumWires = [] := by
  simp only [context, RuntimeCtx.borrowedQuantumWires_addRetained, sampleContext,
    cells_noBorrowed, bankContext, RuntimeCtx.borrowedQuantumWires_addOwnedLayout]
  rfl

/-- Even order one retains nonempty exponent registers under twelve-fold oversampling. -/
public lemma systemCount_pos (P : KnownOrderProblem G) (count : Nat) :
    0 < (context P count).systemCount := by
  have capacity := QuantumAlg.FiniteCyclicDLP.order_lt_fourierModulus P
  change P.order < 2 ^ OrderPreparation.width P at capacity
  have positive : 0 < OrderPreparation.width P := by
    by_contra nonpositive
    have widthZero : OrderPreparation.width P = 0 := by omega
    rw [widthZero] at capacity
    have orderPositive := P.order_pos
    norm_num only [pow_zero] at capacity
    omega
  rw [context_systemCount]
  unfold bankWidth sampleWidth
  omega

variable [Fintype G]

/-- Every complete actual round record retains its own mass at the same physical zero. -/
public lemma round_block_pure (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (record : Store (context P count) ×
      ((model P).HiddenState × (History × (round P slot expansion).Path))) :
    (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds
        (((round P slot expansion).execute
          (sourceEnvironment P) Reference state).block record).marginalLeft :=
  ExecutionState.block_pureKet_of_localMarginal
    ((round P slot expansion).execute (sourceEnvironment P) Reference state)
    (context P count).quantumLayout.zeroLabel (round_pure P slot expansion state) record

/-- The predetermined zero seed restricted to every actual owned physical wire. -/
public def zeroSeed (P : KnownOrderProblem G) (count : Nat) :
    (context P count).quantumLayout.SelectedBasis (context P count).borrowedSelectionᶜ :=
  (context P count).quantumLayout.restrictSelectedBasis (context P count).borrowedSelectionᶜ
    (context P count).quantumLayout.zeroLabel

/-- Owned-wire zero is conditioned on the complete store, service state and path. -/
public lemma round_reinitializedAt (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit.ReinitializedAt (round P slot expansion)
      (sourceEnvironment P) (zeroSeed P count) := by
  have empty : (context P count).borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, noBorrowedQuantum P count]
  have all : (context P count).borrowedSelectionᶜ = Finset.univ := by simp [empty]
  unfold QuantumAlg.Circuit.ReinitializedAt zeroSeed
  rw [all]
  intro Reference History _ state record
  exact StatePromise.pureKet_fullSelection_of_localMarginal (context P count).quantumLayout
    (((round P slot expansion).execute (sourceEnvironment P) Reference state).block record)
    (context P count).quantumLayout.zeroLabel (round_block_pure P slot expansion state record)

/-- Every complete round record has its actual mass at the predetermined owned zero seed. -/
public lemma round_record_reset_matrix (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context P count) Reference ((model P).HiddenState × History))
    (record : Store (context P count) ×
      ((model P).HiddenState × (History × (round P slot expansion).Path))) :
    let observed := DensityOperator.observeSelection (context P count).quantumLayout
      (context P count).borrowedSelectionᶜ Reference
      (((round P slot expansion).execute (sourceEnvironment P) Reference state).block record)
    observed.matrix = (observed.mass : ℝ) •
      (DensityOperator.ofPure (NormalizedVector.ket
        (R := (context P count).quantumLayout.selectedRegister
          (context P count).borrowedSelectionᶜ) (zeroSeed P count))).matrix := by
  have fixed := round_reinitializedAt P slot expansion
  unfold QuantumAlg.Circuit.ReinitializedAt at fixed
  exact (StatePromise.holds_pure_iff _ _).mp (fixed Reference state record)

/-- Every real sample has its own full physical measurement-and-restart certificate. -/
public lemma round_restartCleanup (P : KnownOrderProblem G) {count : Nat} (slot : Fin count)
    (expansion : OrderExpansion P.order) :
    QuantumAlg.Circuit.RestartCleanup (round P slot expansion) (sourceEnvironment P) where
  measured := by
    intro path
    obtain ⟨dimension, present⟩ := ZReset.Bank.zResetBank_measured
      (services := ClassicalFiniteGroupOracle.model G) (oracles := Binary.Oracle.model P)
      (qubits P count) (scratch P count) BitWord.model
      (systemCount_pos P count) path.2.2
    exact ⟨dimension, List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr present)))⟩
  restores := by
    intro Reference History _ state
    exact QuantumAlg.Circuit.borrowedRestored_of_noBorrowedQuantum (round P slot expansion)
      (sourceEnvironment P)
      (noBorrowedQuantum P count) Reference state
  reinitialized := ⟨zeroSeed P count, round_reinitializedAt P slot expansion⟩

end

end QuantumAlg.FiniteCyclicDLP.Reusable
