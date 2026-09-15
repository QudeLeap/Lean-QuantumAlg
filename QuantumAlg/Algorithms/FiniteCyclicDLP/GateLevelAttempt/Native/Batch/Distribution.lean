/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Joint
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Born
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Util.PMF.VectorMass

/-!
# Trace-derived original distribution of the complete finite-cyclic sample batch

Observing the retained finite cells as the original ordered bit strings gives
the original independent vector PMF. This equality is derived from every
reference coefficient of the actual execution, including the empty vector.
The observation is mathematical and adds no runtime packing or copied storage.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

/-- Read each real finite sample as its original ordered terminal bit string. -/
def observedVector (P : KnownOrderProblem G) (count : Nat)
    (value : (CShape.fixedVector count (.fixedVector (sampleWidth P) (.finite 2))).Value) :
    List.Vector (Fin (sampleWidth P) → Bool) count :=
  List.Vector.ofFn fun slot => observedOutcome P (value.get slot)

private theorem constant_fiber {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference)) (coefficient : ℂ)
    (left right : Reference.Index) :
    coefficient * ExecutionState.referenceFiberSum state (fun _ _ => 1) left right =
      ExecutionState.referenceFiberSum state (fun _ _ => coefficient) left right := by
  simp only [ExecutionState.referenceFiberSum, Finset.mul_sum, one_mul]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat)

private theorem terminalIndicator_eq (store : Store (context base noQuantum P count))
    (outcomes : List.Vector (Fin (sampleWidth P) → Bool) count) :
    terminalIndicator base noQuantum P count count id outcomes.get store =
      if observedVector P count (store.read (samplesInput base noQuantum P count)) = outcomes
      then 1 else 0 := by
  let actual := observedVector P count (store.read (samplesInput base noQuantum P count))
  have coordinate (index : Fin count) :
      actual.get index = observedOutcome P (store.read (samples base noQuantum P count index)) := by
    simp only [actual, observedVector, List.Vector.get_ofFn]
    rfl
  by_cases same : actual = outcomes
  · rw [if_pos same]
    unfold terminalIndicator
    apply Finset.prod_eq_one
    intro index _
    have value := (coordinate index).symm.trans (congrArg (fun vector => vector.get index) same)
    exact if_pos value
  · rw [if_neg same]
    have different : ∃ index,
        observedOutcome P (store.read (samples base noQuantum P count index)) ≠
          outcomes.get index := by
      by_contra none
      push Not at none
      apply same
      apply List.Vector.ext
      intro index
      exact (coordinate index).trans (none index)
    obtain ⟨index, different⟩ := different
    exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg different)

/-- The complete real code has the original independent vector law on every normalized input. -/
theorem nativeFiniteCyclicBatch_code_toPMF
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (normalized : state.IsNormalized) :
    ((((code base noQuantum P count B ux).execute Reference state).toPMF
      (((code base noQuantum P count B ux).execute_mass Reference state).trans normalized)).map
        (fun entry => observedVector P count
          (entry.1.read (samplesInput base noQuantum P count)))) =
      PMF.independentReplicateVector (outcomePMF P B ux) count := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
  intro outcomes left right
  have observed := nativeFiniteCyclicBatch_code_reference base noQuantum P count B ux
    (.fixedVector (fun index : Fin 0 => Fin.elim0 index) : CInputRef base (.fixedVector 0 .bit))
    state (fun _ => (1 : ℂ)) outcomes.get left right
  simp only [one_mul] at observed
  simp_rw [terminalIndicator_eq] at observed
  have probability :
      (∏ index : Fin count, ((outcomePMF P B ux (outcomes.get index)).toReal : ℂ)) =
        ((PMF.independentReplicateVector (outcomePMF P B ux) count outcomes).toReal : ℂ) := by
    rw [PMF.independentReplicateVector_toReal_prod, Complex.ofReal_prod]
  rw [probability] at observed
  exact observed.trans (constant_fiber state _ left right)

/-- The complete output's actual raw samples have the same trace-derived independent law. -/
theorem nativeFiniteCyclicBatch_run_outputDistribution
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum P count B ux).outputDistribution input).map (observedVector P count) =
      PMF.independentReplicateVector (outcomePMF P B ux) count := by
  rw [AlgorithmRun.outputDistribution, PMF.map_comp]
  let entered : State base Reference (Store base) :=
    input.state.mapClassical (fun store => (store, store))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun store => (store, store))
  exact nativeFiniteCyclicBatch_code_toPMF base noQuantum P count B ux entered normalized

/-- These are exactly the original concrete samples used by the existing recovery mathematics. -/
theorem nativeFiniteCyclicBatch_run_outputDistribution_concrete
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum P count B ux).outputDistribution input).map (observedVector P count) =
      PMF.independentReplicateVector
        (Concrete.BornBridge.outcomePMF (circuitAccess P B ux)) count :=
  (nativeFiniteCyclicBatch_run_outputDistribution base noQuantum P count B ux input).trans
    (congrArg (fun distribution => PMF.independentReplicateVector distribution count)
      (nativeFiniteCyclic_outcomePMF_eq_concrete P B ux))

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
