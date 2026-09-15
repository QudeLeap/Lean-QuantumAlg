/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Reuse
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# Trace-derived probabilities of the actual original ECDLP sampler

The same complete execution determines the finite output law. Observing the
stored two-valued cells in their original order gives the original terminal
Born PMF, both after initial allocation and after paid reuse on arbitrary
incoming states. The conversion is a mathematical observation of existing
storage, with no additional runtime computation or sampled-law premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem constant_fiber {C : Type} [Fintype C] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference)) (coefficient : ℂ)
    (left right : Reference.Index) :
    coefficient * ExecutionState.referenceFiberSum state (fun _ _ => 1) left right =
      ExecutionState.referenceFiberSum state (fun _ _ => coefficient) left right := by
  simp only [ExecutionState.referenceFiberSum, Finset.mul_sum, one_mul]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

/-- Initial real allocation and sampling have the original Born law on every normalized input. -/
theorem nativeECDLP_first_outcome_toPMF
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (normalized : state.IsNormalized) :
    ((((run base noQuantum I B A).code.execute Reference state).toPMF
      (((run base noQuantum I B A).code.execute_mass Reference state).trans normalized)).map
        (fun entry => observedOutcome I (entry.1.read (sampleInput base noQuantum I)))) =
      outcomePMF I B A := by
  classical
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
  intro outcome left right
  have observed := nativeECDLP_first_outcome_reference base noQuantum I B A
    (.fixedVector (fun index : Fin 0 => Fin.elim0 index) : CInputRef base (.fixedVector 0 .bit))
    state (fun _ => (1 : ℂ)) outcome left right
  simp only [one_mul] at observed
  exact observed.trans (constant_fiber state _ left right)

/-- Every paid reuse round has the same trace-derived Born law without an initial-state promise. -/
theorem nativeECDLP_reusedSample_outcome_toPMF
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History)
    (normalized : state.IsNormalized) :
    ((((reusedSample base noQuantum I B A).execute Reference state).toPMF
      (((reusedSample base noQuantum I B A).execute_mass Reference state).trans normalized)).map
        (fun entry => observedOutcome I (entry.1.read (sampleInput base noQuantum I)))) =
      outcomePMF I B A := by
  classical
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum state _ normalized
  intro outcome left right
  have observed := nativeECDLP_reusedSample_outcome_reference base noQuantum I B A
    (.fixedVector (fun index : Fin 0 => Fin.elim0 index) : CInputRef base (.fixedVector 0 .bit))
    state (fun _ => (1 : ℂ)) outcome left right
  simp only [one_mul] at observed
  exact observed.trans (constant_fiber state _ left right)

/-- The actual complete single-sample run exposes those same stored outcomes. -/
theorem nativeECDLP_run_outputDistribution
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} (input : Execution.Input base Reference) :
    ((run base noQuantum I B A).outputDistribution input).map (observedOutcome I) =
      outcomePMF I B A := by
  rw [AlgorithmRun.outputDistribution, PMF.map_comp]
  let entered : State base Reference (Store base) :=
    input.state.mapClassical (fun store => (store, store))
  have normalized := input.state.mapClassical_normalized input.normalized
    (fun store => (store, store))
  exact nativeECDLP_first_outcome_toPMF base noQuantum I B A entered normalized

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
