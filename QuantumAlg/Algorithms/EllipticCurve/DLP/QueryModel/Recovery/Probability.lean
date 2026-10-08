/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Candidate
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.SuccessFloor
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Selected
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Event
import all QuantumAlg.Core.Execution.State.Effect

/-!
# The actual candidate floor beside all persistent recovery cells

The original selected raw family is contained in the complete native
candidate condition. The existing seven-cell coordinate law keeps actual
probability mass, quantum references and retained classical correlations.
The result therefore applies directly to every real unnormalized failure
fiber of the sampled recovery loop, without an independent-sampling premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution FiniteCyclicDLP.Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

private theorem indicator_weight {R : Register} (state : DensityOperator R)
    (condition : Prop) [Decidable condition] :
    (if condition then Effect.one R else Effect.zero R).weight state =
      if condition then state.mass else 0 := by
  split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero]

private theorem family_mass {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
    {R : Register} (state : ExecutionState C R) (read : C → D) (family : Finset D) :
    family.sum (fun outcome => ((state.mapClassical read).block outcome).mass) =
      state.effectWeight (fun record => if read record ∈ family then
        Effect.one R else Effect.zero R) := by
  rw [← ExecutionState.effectWeight_mapClassical_decision (inferInstance : DecidableEq D)
    state read (fun outcome => if outcome ∈ family then Effect.one R else Effect.zero R)]
  simp only [ExecutionState.effectWeight, indicator_weight, Finset.sum_ite_mem_eq]

private def selectedEvent (I : ECDLPInstance E) (input : SecretInput (problem I))
    (sample : CShape.Value (.fixedVector (scalarWidth I + scalarWidth I) (.finite 2))) : Bool :=
  decide (Sampling.observedOutcome I sample ∈ selectedRawOutcomeFamily (problem I) input)

private theorem selected_event_accepted (I : ECDLPInstance E)
    (nontrivial : 2 ≤ (problem I).order) (input : SecretInput (problem I))
    (sample : CShape.Value (.fixedVector (scalarWidth I + scalarWidth I) (.finite 2)))
    (selected : selectedEvent I input sample = true) :
    SampleAccepted (curve E) (modulus I nontrivial)
      I.basePoint.toMathlib I.targetPoint.toMathlib sample := by
  have member := of_decide_eq_true selected
  rw [selectedRawOutcomeFamily] at member
  obtain ⟨unit, _, same⟩ := Finset.mem_image.mp member
  exact selectedOutcome_accepted I nontrivial input unit sample same.symm

private theorem indicator_weight_mono {R : Register} (state : DensityOperator R)
    (first second : Prop) [Decidable first] [Decidable second] (included : first → second) :
    (if first then Effect.one R else Effect.zero R).weight state ≤
      (if second then Effect.one R else Effect.zero R).weight state := by
  by_cases selected : first
  · simp only [selected, included selected, if_true, le_refl]
  · by_cases eligible : second
    · simp only [selected, eligible, if_false, if_true, Effect.weight_one, Effect.weight_zero]
      exact state.mass_nonneg
    · simp only [selected, eligible, if_false, le_refl]

private theorem selected_weight_le (I : ECDLPInstance E)
    (nontrivial : 2 ≤ (problem I).order) (input : SecretInput (problem I))
    {ctx : RuntimeCtx .quantum} {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (sample : CInputRef ctx (.fixedVector (scalarWidth I + scalarWidth I) (.finite 2))) :
    state.effectWeight (fun record => if selectedEvent I input (record.1.read sample) = true then
      Effect.one (ctx.register.prod Reference) else Effect.zero (ctx.register.prod Reference)) ≤
      state.effectWeight (fun record => if SampleAccepted (curve E) (modulus I nontrivial)
        I.basePoint.toMathlib I.targetPoint.toMathlib (record.1.read sample) then
          Effect.one (ctx.register.prod Reference)
        else Effect.zero (ctx.register.prod Reference)) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro record _
  exact indicator_weight_mono (state.block record) _ _
    (selected_event_accepted I nontrivial input (record.1.read sample))

/-- Actual sampling beside the existing seven cells retains the complete candidate mass floor. -/
theorem ecdlpRecovery_sample_weight_bound (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (input : SecretInput (problem I))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State
      (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)) Reference
        ((Sampling.executionModel I A).HiddenState × History)) :
    state.mass * Sampling.Reuse.successFloor I ≤
      ((underPersistent (Sampling.Reuse.code I A expansion)
        (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (fieldWidth E)
        (scalarWidth I)).execute Reference state).effectWeight (fun record =>
          if SampleAccepted (curve E) (modulus I nontrivial)
              I.basePoint.toMathlib I.targetPoint.toMathlib
              (record.1.read (persistentInput (fieldWidth E) (scalarWidth I)
                (Sampling.Reuse.sampleInput I))) then
            Effect.one ((persistentCtx (Sampling.Reuse.context I) (fieldWidth E)
              (scalarWidth I)).register.prod Reference)
          else Effect.zero ((persistentCtx (Sampling.Reuse.context I) (fieldWidth E)
              (scalarWidth I)).register.prod Reference)) := by
  have original := Sampling.Reuse.ecdlpReuse_selectedFamily_mass_floor I A expansion input
    (underPersistentSplitState (fieldWidth E) (scalarWidth I) state)
  rw [underPersistentSplitState_mass, family_mass] at original
  have actual := underPersistent_eventWeight (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (fieldWidth E) (scalarWidth I) state
    (Sampling.Reuse.sampleInput I) (selectedEvent I input)
  simp only [selectedEvent, decide_eq_true_eq] at actual
  have inclusion := selected_weight_le I nontrivial input
    ((underPersistent (Sampling.Reuse.code I A expansion)
      (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (fieldWidth E)
      (scalarWidth I)).execute Reference state)
    (persistentInput (fieldWidth E) (scalarWidth I) (Sampling.Reuse.sampleInput I))
  simp only [selectedEvent, decide_eq_true_eq] at inclusion
  exact (original.trans_eq actual.symm).trans inclusion

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
