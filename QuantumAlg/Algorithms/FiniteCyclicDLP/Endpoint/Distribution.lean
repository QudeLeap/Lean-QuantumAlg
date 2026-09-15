/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Recovery
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Endpoint.Sampling
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Original checked-candidate law of the actual complete finite-cyclic run

The actual sample state flows through the real result allocation and every
classical attempt. Its optional output distribution is the original ordered
sample law pushed through the checked first-success fold. The input fixes
only the original target and permits an arbitrary external reference.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint

open Execution
open GateLevelAttempt.Native (sampleWidth)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

private theorem observed_pmf_congr {C D Value : Type}
    [Fintype C] [Fintype D] [Fintype Value] {R : Register}
    (first : ExecutionState C R) (second : ExecutionState D R)
    (firstNormalized : first.IsNormalized) (secondNormalized : second.IsNormalized)
    (firstRead : C → Value) (secondRead : D → Value)
    (equal : first.mapClassical firstRead = second.mapClassical secondRead) :
    (first.toPMF firstNormalized).map firstRead =
      (second.toPMF secondNormalized).map secondRead := by
  have mapped : (first.mapClassical firstRead).toPMF
        (first.mapClassical_normalized firstNormalized firstRead) =
      (second.mapClassical secondRead).toPMF
        (second.mapClassical_normalized secondNormalized secondRead) := by
    apply PMF.ext
    intro value
    exact congrArg (fun state : ExecutionState Value R =>
      ENNReal.ofReal (state.block value).mass) equal
  exact (ExecutionState.toPMF_mapClassical first firstNormalized firstRead).symm.trans
    (mapped.trans (ExecutionState.toPMF_mapClassical second secondNormalized secondRead))

/-- Interpret the actual joint observation using exactly the original checked selector. -/
def recoveredJointValue (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    (joint : CShape.Word (orderWidth P) ×
      List.Vector (Fin (sampleWidth P) → Bool) (retryCount P)) :
    CShape.Value (.option (.unsignedWord (orderWidth P))) :=
  recoveredValue P B A (rawSamples P (retryCount P) joint.2) joint.1

/-- The original independent raw samples determine the complete checked optional result. -/
def outputLaw (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P) :
    PMF (CShape.Value (.option (.unsignedWord (orderWidth P)))) :=
  (sampledJointLaw P B A).map (recoveredJointValue P B A)

private theorem code_observed (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre P) Reference History) :
    ((code P B A).execute Reference state).mapClassical
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef)) =
      ((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
        P (retryCount P) B A.ux).execute Reference state).mapClassical
          (fun entry => recoveredJointValue P B A (sampledJoint P entry.1)) := by
  let sampler := GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
    P (retryCount P) B A.ux
  let sampled := sampler.execute Reference state
  have observed := (sequence_read sampler (retainedRecovery P B A) state
    (fun store => store.read (.storage (outputRef P).toCStorageRef))).trans
      (finiteCyclic_retainedRecovery_read P B A sampled)
  have jointRead : sampled.mapClassical (fun entry => recoveredValue P B A
      (entry.1.read (GateLevelAttempt.Native.Batch.samplesInput
        (pre P) (input_quantumWires P) P (retryCount P)))
      (entry.1.read (GateLevelAttempt.Native.Batch.liftInput
        (pre P) (input_quantumWires P) P (retryCount P) (targetRef P)))) = sampled.mapClassical
      (fun entry => recoveredJointValue P B A (sampledJoint P entry.1)) := by
    apply congrArg (ExecutionState.mapClassical sampled)
    funext entry
    exact congrArg (fun values => recoveredValue P B A values
      (entry.1.read (GateLevelAttempt.Native.Batch.liftInput
        (pre P) (input_quantumWires P) P (retryCount P) (targetRef P))))
      (rawSamples_observed P (retryCount P)
        (entry.1.read (GateLevelAttempt.Native.Batch.samplesInput
          (pre P) (input_quantumWires P) P (retryCount P)))).symm
  exact observed.trans jointRead

private theorem code_observed_probability (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre P) Reference History) (normalized : state.IsNormalized) :
    ((((code P B A).execute Reference state).toPMF
      (((code P B A).execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))) =
      (((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
        P (retryCount P) B A.ux).execute Reference state).toPMF
          (((GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
            P (retryCount P) B A.ux).execute_mass Reference state).trans normalized)).map
              (fun entry => recoveredJointValue P B A (sampledJoint P entry.1)) := by
  let sampler := GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
    P (retryCount P) B A.ux
  let sampled := sampler.execute Reference state
  have sampledNormalized := (sampler.execute_mass Reference state).trans normalized
  exact observed_pmf_congr ((code P B A).execute Reference state) sampled
    (((code P B A).execute_mass Reference state).trans normalized) sampledNormalized
    (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))
    (fun entry => recoveredJointValue P B A (sampledJoint P entry.1))
    (code_observed P B A state)

attribute [local irreducible] code GateLevelAttempt.Native.Batch.code
  recoveredJointValue sampledJoint sampledJointLaw

/-- The final actual optional cell has the law derived from the original sampled input. -/
theorem finiteCyclic_code_outputDistribution (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre P) Reference History) (normalized : state.IsNormalized)
    (pinned : targetPinned P A state) :
    ((((code P B A).execute Reference state).toPMF
      (((code P B A).execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read (.storage (outputRef P).toCStorageRef))) =
      outputLaw P B A := by
  let sampler := GateLevelAttempt.Native.Batch.code (pre P) (input_quantumWires P)
    P (retryCount P) B A.ux
  let sampled := sampler.execute Reference state
  have sampledNormalized := (sampler.execute_mass Reference state).trans normalized
  refine (code_observed_probability P B A state normalized).trans ?_
  have source := finiteCyclic_sampledJoint_toPMF P B A state normalized pinned
  exact (PMF.map_comp (fun entry => sampledJoint P entry.1)
    (sampled.toPMF sampledNormalized) (recoveredJointValue P B A)).symm.trans
      (congrArg (PMF.map (recoveredJointValue P B A)) source)

/-- The complete actual run needs only its original fixed borrowed target value. -/
theorem finiteCyclic_run_outputDistribution (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (A : Access P)
    {Reference : Register} (input : Execution.Input (pre P) Reference)
    (originalTarget : ∀ store, 0 < (input.state.block store).mass →
      store.read (targetRef P) = targetValue A) :
    (run P B A).outputDistribution input = outputLaw P B A := by
  let entered : State (pre P) Reference (Store (pre P)) :=
    input.state.mapClassical (fun store => (store, store))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun store => (store, store))
  have pinned : targetPinned P A entered := by
    intro entry positive
    change 0 < ((input.state.mapClassical (fun store => (store, store))).block entry).mass
      at positive
    obtain ⟨store, same, supported⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff input.state
        (fun store => (store, store)) entry).mp
          (by
            simp only [ExecutionState.mapClassical_block_mass] at positive ⊢
            apply lt_of_lt_of_eq positive
            apply Finset.sum_congr rfl
            intro store _
            split_ifs <;> rfl)
    cases same
    exact originalTarget store supported
  exact finiteCyclic_code_outputDistribution P B A entered normalized pinned

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Endpoint
