/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Samples
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Actual joint sampling law with the original borrowed target

The original input fixes only its one borrowed target word. Every reference
state and correlation remains admissible. The actual full-reference sample
law fixes that same target alongside the original independent bit strings,
before any classical recovery or optional output is observed.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open Execution
open GateLevelAttempt.Native (sampleWidth)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

/-- The input's sole classical operand is the original encoded target. -/
def targetPinned (P : KnownOrderProblem G) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre P) Reference History) : Prop :=
  ∀ entry, 0 < (state.block entry).mass → entry.1.read (targetRef P) = targetValue A

/-- Joint mathematical observation of the real borrowed target and all original raw samples. -/
def sampledJoint (P : KnownOrderProblem G) (store : Store
    (GateLevelAttempt.Native.Batch.context (pre P) (input_quantumWires P) P (retryCount P))) :
    CShape.Word (orderWidth P) × List.Vector (Fin (sampleWidth P) → Bool) (retryCount P) :=
  (store.read (GateLevelAttempt.Native.Batch.liftInput (pre P) (input_quantumWires P)
      P (retryCount P) (targetRef P)),
    GateLevelAttempt.Native.Batch.observedVector P (retryCount P)
      (store.read (GateLevelAttempt.Native.Batch.samplesInput (pre P) (input_quantumWires P)
        P (retryCount P))))

/-- The original sample law carries the unchanged actual target in its first coordinate. -/
def sampledJointLaw (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    PMF (CShape.Word (orderWidth P) ×
      List.Vector (Fin (sampleWidth P) → Bool) (retryCount P)) :=
  (PMF.independentReplicateVector (GateLevelAttempt.Native.outcomePMF P B A.ux)
    (retryCount P)).map (fun outcomes => (targetValue A, outcomes))

private theorem jointLaw_apply (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (target : CShape.Word (orderWidth P))
    (outcomes : List.Vector (Fin (sampleWidth P) → Bool) (retryCount P)) :
    sampledJointLaw P B A (target, outcomes) =
      if target = targetValue A then
        PMF.independentReplicateVector (GateLevelAttempt.Native.outcomePMF P B A.ux)
          (retryCount P) outcomes else 0 := by
  by_cases same : target = targetValue A
  · subst target
    rw [if_pos rfl]
    exact PMF.map_apply_of_injective _ (fun values => (targetValue A, values))
      (fun _ _ equal => congrArg Prod.snd equal) outcomes
  · rw [if_neg same, sampledJointLaw, PMF.map_apply]
    simp only [Prod.mk.injEq, same, false_and, if_false, tsum_zero]

private theorem pinned_reference (P : KnownOrderProblem G) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre P) Reference History) (pinned : targetPinned P A state)
    (target : CShape.Word (orderWidth P)) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum state
        (fun entry _ => if entry.1.read (targetRef P) = target then 1 else 0) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => if targetValue A = target then 1 else 0) left right := by
  unfold ExecutionState.referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro entry _
  by_cases positive : 0 < (state.block entry).mass
  · exact congrArg (fun value : CShape.Word (orderWidth P) =>
      (if value = target then (1 : ℂ) else 0) *
        (state.block entry).matrix (basis, left) (basis, right)) (pinned entry positive)
  · have zero := le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    rw [state.block_eq_zero_of_mass_eq_zero entry zero, DensityOperator.zero_matrix]
    simp only [Matrix.zero_apply, mul_zero]

/-- The original actual code jointly preserves its target and generates the original sample law. -/
theorem finiteCyclic_sampledJoint_toPMF (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre P) Reference History) (normalized : state.IsNormalized)
    (pinned : targetPinned P A state) :
    ((((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
      P (retryCount P) B A.ux).execute Reference state).toPMF
        (((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
          P (retryCount P) B A.ux).execute_mass Reference state).trans normalized)).map
            (fun entry => sampledJoint P entry.1)) = sampledJointLaw P B A := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
  rintro ⟨target, outcomes⟩ left right
  have sampled := GateLevelAttempt.Native.Batch.nativeFiniteCyclicBatch_code_reference
    (pre P) (input_quantumWires P) P (retryCount P) B A.ux (targetRef P) state
    (fun value => if value = target then (1 : ℂ) else 0) outcomes.get left right
  simp_rw [GateLevelAttempt.Native.Batch.terminalIndicator_eq] at sampled
  have indicator : ∀ store : Store
      (GateLevelAttempt.Native.Batch.context (pre P) (input_quantumWires P) P (retryCount P)),
      (if store.read (GateLevelAttempt.Native.Batch.liftInput (pre P) (input_quantumWires P)
          P (retryCount P) (targetRef P)) = target then (1 : ℂ) else 0) *
        (if GateLevelAttempt.Native.Batch.observedVector P (retryCount P)
          (store.read (GateLevelAttempt.Native.Batch.samplesInput (pre P) (input_quantumWires P)
            P (retryCount P))) = outcomes then 1 else 0) =
      if sampledJoint P store = (target, outcomes) then 1 else 0 := by
    intro store
    simp only [sampledJoint, Prod.mk.injEq]
    split_ifs <;> simp_all
  simp_rw [indicator] at sampled
  rw [pinned_reference P A state pinned target left right] at sampled
  have product :
      (∏ index : Fin (retryCount P),
        ((GateLevelAttempt.Native.outcomePMF P B A.ux (outcomes.get index)).toReal : ℂ)) =
      ((PMF.independentReplicateVector (GateLevelAttempt.Native.outcomePMF P B A.ux)
        (retryCount P) outcomes).toReal : ℂ) := by
    rw [PMF.independentReplicateVector_toReal_prod, Complex.ofReal_prod]
  rw [product] at sampled
  refine sampled.trans ?_
  rw [jointLaw_apply]
  by_cases same : target = targetValue A
  · simp only [same, if_true]
    simp only [ExecutionState.referenceFiberSum, Finset.mul_sum, one_mul]
  · simp only [same, Ne.symm same, if_false, ENNReal.toReal_zero, Complex.ofReal_zero]
    simp only [ExecutionState.referenceFiberSum, zero_mul, Finset.sum_const_zero, mul_zero]

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
