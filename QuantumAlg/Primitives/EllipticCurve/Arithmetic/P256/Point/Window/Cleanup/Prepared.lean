/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Restart
import all QuantumAlg.Core.Execution.Restart.Deterministic
import all QuantumAlg.Core.Execution.Pure.Selection
import all QuantumAlg.Core.Execution.Local.Marginals

/-!
# Re-preparation after the actual complete point-bank cleanup

The supplied unitary is real Circuit syntax and its action on the fixed
zero ket is proved separately. All original Store, hidden-state, history
and path records survive the composition. No input promise is required.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Cleanup.Parameters

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx)

/-- The actual reset's complete local marginal is zero at its original mass. -/
lemma circuit_pure_local
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (record : Store ctx × (services.HiddenState ×
      (History × (parameters.circuit (services := services)).Path))) :
    (StatePromise.pure (NormalizedVector.ket parameters.zeroLabel)).Holds
      ((parameters.circuit.execute environment Reference state).block record).marginalLeft := by
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  rw [DensityOperator.marginalLeft_matrix]
  apply Finset.sum_eq_zero
  intro reference _
  exact parameters.circuit_zero_row environment state record row column reference reference
    different

private lemma pure_applyUnitary {R : Register} (operator : UnitaryOperator R)
    (state : DensityOperator R) (target : NormalizedVector R)
    (promised : (StatePromise.pure target).Holds state) :
    (StatePromise.pure (operator.apply target)).Holds
      (DensityOperator.applyUnitary operator state) := by
  rw [StatePromise.holds_pure_iff] at promised ⊢
  rw [DensityOperator.applyUnitary_mass, DensityOperator.ofPure_apply,
    DensityOperator.applyUnitary_matrix, DensityOperator.applyUnitary_matrix, promised,
    Matrix.mul_smul, smul_mul_assoc]

/-- The original cleanup followed by a real native instruction on exactly the same bank. -/
def prepared (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  parameters.circuit.seq (.unitary program)

/-- Every complete record has the proved fixed unitary image of the actual reset seed. -/
lemma prepared_reinitializedAt
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (seed : ctx.quantumLayout.Basis)
    (action : (program.matrix environment.quantum).apply
      (NormalizedVector.ket parameters.zeroLabel) = NormalizedVector.ket seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (parameters.prepared program) environment
      (ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ seed) := by
  have empty : ctx.borrowedSelection = ∅ := by
    ext wire
    simp [RuntimeCtx.mem_borrowedSelection, noBorrowed]
  have all : ctx.borrowedSelectionᶜ = Finset.univ := by simp only [empty, Finset.compl_empty]
  unfold Circuit.ReinitializedAt
  rw [all]
  intro Reference History _ state record
  dsimp only [prepared]
  rw [Circuit.execute_seq]
  unfold State.mapHistory
  apply Circuit.RestartCleanup.selectedPureMapDecision ctx.quantumLayout Finset.univ Reference _
    (((Circuit.unitary program :
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false)).execute
        environment Reference (parameters.circuit.execute environment Reference state))
    (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
    (NormalizedVector.ket (ctx.quantumLayout.restrictSelectedBasis Finset.univ seed)) _ record
  rintro ⟨store, hidden, history, path⟩
  cases path
  rw [Circuit.execute_unitary_block]
  apply StatePromise.pureKet_fullSelection_of_localMarginal
  rw [DensityOperator.localUnitary_marginalLeft, ← action]
  exact pure_applyUnitary (program.matrix environment.quantum) _ _
    (parameters.circuit_pure_local environment state (store, hidden, history))

/-- The same actual measured cleanup remains restartable after proved fixed native loading. -/
lemma prepared_restartCleanup
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (seed : ctx.quantumLayout.Basis)
    (action : (program.matrix environment.quantum).apply
      (NormalizedVector.ket parameters.zeroLabel) = NormalizedVector.ket seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (parameters.prepared program) environment where
  measured := by
    intro path
    obtain ⟨dimension, present⟩ := parameters.circuit_measured path.1
    exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (parameters.prepared program) environment
      noBorrowed Reference state
  reinitialized := ⟨ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ seed,
    parameters.prepared_reinitializedAt environment program seed action noBorrowed⟩

end

end Cleanup.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
