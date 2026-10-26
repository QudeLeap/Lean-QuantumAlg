/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup.Prepared
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Observe.Grouping
import all QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Base.Gate.Effect.BasisSlice
import all QuantumAlg.Core.Base.State.Density.BasisSupport

/-!
# Original conditional reference blocks after the actual fixed restart

Every complete restart record has the same physical seed. Its reference
slice has exactly that record's mass, including zero-mass records.
Uniform bounds on pure references therefore extend to the actual conditional
mixed block without division, normalization or an independence assumption.
This is an execution identity and requires no ownership-role premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical DensityOperator.marginalLeft
  DensityOperator.ofPure Initialization.physicalSeed Initialization.placedProgram
  StatePromise.Holds

private lemma localPureMapDecision {C D : Type} [Fintype C] [Fintype D]
    {R Reference : Register} (decision : DecidableEq D)
    (state : ExecutionState C (R.prod Reference)) (read : C → D)
    (target : NormalizedVector R)
    (holds : ∀ entry, (StatePromise.pure target).Holds (state.block entry).marginalLeft)
    (result : D) :
    (StatePromise.pure target).Holds
      ((@ExecutionState.mapClassical C D _ _ _ decision state read).block result).marginalLeft := by
  have decisionSame : decision = Classical.decEq D := Subsingleton.elim _ _
  subst decision
  have grouped : (StatePromise.pure target).Holds
      (((state.mapClassical read).marginalLeft).block result) := by
    rw [ExecutionState.executionState_marginalLeft_mapClassical]
    exact ExecutionState.mapClassical_pure state.marginalLeft read target holds result
  simpa only [ExecutionState.marginalLeft] using grouped

private lemma prepared_pure_local {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (cleanup : Cleanup.Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (seed : ctx.quantumLayout.Basis)
    (action : (program.matrix environment.quantum).apply
      (NormalizedVector.ket cleanup.zeroLabel) = NormalizedVector.ket seed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (record : Store ctx × (services.HiddenState ×
      (History × (cleanup.prepared (services := services) program).Path))) :
    (StatePromise.pure (NormalizedVector.ket seed)).Holds
      (((cleanup.prepared (services := services) program).execute environment Reference state).block
        record).marginalLeft := by
  dsimp only [Cleanup.Parameters.prepared]
  rw [Circuit.execute_seq]
  unfold State.mapHistory
  apply localPureMapDecision _
    (((Circuit.unitary program :
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false)).execute
        environment Reference
          ((cleanup.circuit (services := services)).execute environment Reference state))
    (fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
    (NormalizedVector.ket seed) _ record
  rintro ⟨store, hidden, history, path⟩
  cases path
  rw [Circuit.execute_unitary_block, DensityOperator.localUnitary_marginalLeft, ← action]
  exact Cleanup.Parameters.pure_applyUnitary (program.matrix environment.quantum) _ _
    (cleanup.circuit_pure_local environment state (store, hidden, history))

private lemma diagonal_zero_of_local_pure {R Reference : Register}
    (state : DensityOperator (R.prod Reference)) (seed : R.Index)
    (pure : (StatePromise.pure (NormalizedVector.ket seed)).Holds state.marginalLeft)
    (basis : R.Index) (different : basis ≠ seed) :
    state.marginalLeft.matrix basis basis = 0 := by
  rw [StatePromise.holds_pure_iff] at pure
  rw [pure, Matrix.smul_apply, DensityOperator.ofPure_matrix]
  simp only [NormalizedVector.ket_apply, if_neg different, zero_mul, smul_zero]

private lemma factor_of_local_pure {R Reference : Register}
    (state : DensityOperator (R.prod Reference)) (seed : R.Index)
    (pure : (StatePromise.pure (NormalizedVector.ket seed)).Holds state.marginalLeft)
    (left right : R.Index) (refLeft refRight : Reference.Index) :
    state.matrix (left, refLeft) (right, refRight) =
      NormalizedVector.ket seed left * state.matrix (seed, refLeft) (seed, refRight) *
        star (NormalizedVector.ket seed right) := by
  by_cases sameLeft : left = seed
  · subst left
    by_cases sameRight : right = seed
    · subst right
      simp only [NormalizedVector.ket_apply, if_true, one_mul, star_one, mul_one]
    · rw [DensityOperator.joint_column_zero_of_marginal_diagonal_zero state right
        (diagonal_zero_of_local_pure state seed pure right sameRight) refRight (seed, refLeft)]
      simp only [NormalizedVector.ket_apply, if_neg sameRight, star_zero, mul_zero]
  · rw [DensityOperator.joint_row_zero_of_marginal_diagonal_zero state left
      (diagonal_zero_of_local_pure state seed pure left sameLeft) refLeft (right, refRight)]
    simp only [NormalizedVector.ket_apply, if_neg sameLeft, zero_mul]

namespace Inputs

attribute [local irreducible] restart Circuit.execute Circuit.pathFintype

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (output : CWriteRef ctx (.finite 2))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))

variable
    (record : Store ctx × (services.HiddenState ×
      (History × (original.restart (services := services) output).Path)))

/-- The existing reset wires and paid output cell, named once for proof elaboration. -/
def restartCleanup : Cleanup.Parameters ctx := ⟨original.sameWires, output⟩

/-- The physical basis label loaded by the existing restart program. -/
def restartSeed : ctx.register.Index :=
  Initialization.physicalSeed (original.restartCleanup output) original.seedX original.seedY

/-- The conditional quantum block of one complete record of the actual fixed restart. -/
def restartBlock : DensityOperator (ctx.register.prod Reference) :=
  ((original.restart (services := services) output).execute environment Reference state).block
    record

private lemma restart_pure_local :
    (StatePromise.pure (NormalizedVector.ket (R := ctx.register)
      (original.restartSeed output))).Holds
      (original.restartBlock output environment state record).marginalLeft := by
  unfold restartBlock
  let cleanup : Cleanup.Parameters ctx := original.restartCleanup output
  dsimp only [restartSeed, restartCleanup] at ⊢
  unfold restart at record ⊢
  rw [Circuit.execute_identity_embed]
  exact prepared_pure_local cleanup environment
    (Initialization.placedProgram cleanup original.seedX original.seedY)
    (Initialization.physicalSeed cleanup original.seedX original.seedY)
    (Initialization.placedProgram_zero cleanup original.seedX original.seedY environment.quantum)
    state record

/-- Every complete record of the actual identity-embedded restart has the
same fixed pure seed on the complete physical bank, with arbitrary reference. -/
lemma restart_pure_fullSelection :
    (StatePromise.pure (NormalizedVector.ket
      (R := ctx.quantumLayout.selectedRegister Finset.univ)
      (ctx.quantumLayout.restrictSelectedBasis Finset.univ
        (original.restartSeed output)))).Holds
      (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
        (original.restartBlock output environment state record)) := by
  exact StatePromise.pureKet_fullSelection_of_localMarginal
    ctx.quantumLayout
    (original.restartBlock output environment state record)
    (original.restartSeed output)
    (original.restart_pure_local output environment state record)

/-- Each actual reset record retains every entry of its original conditional reference block. -/
lemma restart_block_factor
    (left right : ctx.register.Index) (refLeft refRight : Reference.Index) :
    let seed : ctx.register.Index := original.restartSeed output
    let block : DensityOperator (ctx.register.prod Reference) :=
      original.restartBlock output environment state record
    block.matrix (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := ctx.register) seed left *
        block.matrix (seed, refLeft) (seed, refRight) *
        star (NormalizedVector.ket (R := ctx.register) seed right) :=
  factor_of_local_pure _ _ (original.restart_pure_local output environment state record)
    left right refLeft refRight

/-- The actual conditional reference slice has exactly its full restart record's mass. -/
lemma restart_reference_mass :
    let seed : ctx.register.Index := original.restartSeed output
    let block : DensityOperator (ctx.register.prod Reference) :=
      original.restartBlock output environment state record
    (block.basisSlice seed).mass = block.mass :=
  DensityOperator.basisSlice_mass_of_factor _ _
    (original.restart_block_factor output environment state record)

/-- A pure-reference bound applies to the same actual, possibly mixed, complete restart record. -/
lemma restart_block_weight_lower
    (observed : Effect (ctx.register.prod Reference)) (lower : ℝ)
    (bound : ∀ reference : NormalizedVector Reference,
      lower ≤ (observed.basisSliceEffect
        (original.restartSeed output)).weight (DensityOperator.ofPure reference)) :
    (original.restartBlock output environment state record).mass * lower ≤
      observed.weight (original.restartBlock output environment state record) :=
  Effect.mass_mul_le_weight_of_basis_factor observed _ _ lower
    (original.restart_block_factor output environment state record) bound

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
