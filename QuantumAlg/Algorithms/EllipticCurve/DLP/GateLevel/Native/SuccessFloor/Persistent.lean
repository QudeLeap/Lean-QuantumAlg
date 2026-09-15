/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.SuccessFloor.Weight
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.SuccessFloor.Selection
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Event

/-!
# Original ECDLP candidate floor beside the persistent recovery cells

The actual finite cells are decoded in their original order. The selected
family therefore gives the original recovered scalar and both checked flags.
Its natural scalar satisfies the public point equation. Lifting the same
paid sampling circuit beside all seven existing cells preserves that event
weight for arbitrary full states, including arbitrary old cell values and
reference correlations. No secret or success certificate enters the code.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem selected_indicator_le {R : Register} (state : DensityOperator R)
    (selected accepted : Prop) [Decidable selected] [Decidable accepted]
    (included : selected → accepted) :
    (if selected then Effect.one R else Effect.zero R).weight state ≤
      (if accepted then Effect.one R else Effect.zero R).weight state := by
  by_cases found : selected
  · simp only [found, included found, if_true, le_refl]
  · by_cases valid : accepted
    · simp only [found, valid, if_false, if_true, Effect.weight_one, Effect.weight_zero]
      exact state.mass_nonneg
    · simp only [found, valid, if_false, le_refl]

attribute [local irreducible] persistentCtx context reusedSample underPersistent
  FiniteCyclicDLP.Canonical.Probability.selectedRawOutcomeFamily

/-- The actual reused sample has the original candidate floor beside all seven existing cells. -/
theorem nativeECDLP_persistent_candidate_weight_bound
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx (context base noQuantum I) (Layout.fieldWidth E)
      (FiniteCyclicDLP.orderWidth (problem I))) Reference History) :
    state.mass * FiniteCyclicDLP.Concrete.Amplification.attemptFloor (problem I) ≤
      ((underPersistent (reusedSample base noQuantum I B A)
        (nativeECDLP_reusedSample_isLocal base noQuantum I B A) (Layout.fieldWidth E)
        (FiniteCyclicDLP.orderWidth (problem I))).execute Reference state).effectWeight
        (fun record =>
          if SampleAccepted (Layout.curveSpec E) (recoveryModulus I)
              I.basePoint.toMathlib I.targetPoint.toMathlib
              (record.1.read (persistentInput (Layout.fieldWidth E)
                (FiniteCyclicDLP.orderWidth (problem I)) (sampleInput base noQuantum I))) then
            Effect.one ((persistentCtx (context base noQuantum I) (Layout.fieldWidth E)
              (FiniteCyclicDLP.orderWidth (problem I))).register.prod Reference)
          else Effect.zero ((persistentCtx (context base noQuantum I) (Layout.fieldWidth E)
            (FiniteCyclicDLP.orderWidth (problem I))).register.prod Reference)) := by
  let code := reusedSample base noQuantum I B A
  have supported := nativeECDLP_reusedSample_isLocal base noQuantum I B A
  let event := fun value => decide (observedOutcome I value ∈
    FiniteCyclicDLP.Probability.selectedOutcomeFamily (problem I) (input I))
  have floor := nativeECDLP_reusedSample_selected_weight_ge base noQuantum I B A
    (underPersistentSplitState (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I)) state)
  rw [underPersistentSplitState_mass,
    FiniteCyclicDLP.Concrete.Amplification.selectedOutcomeFamilyLowerBound_eq_ofReal_attemptFloor,
    ENNReal.toReal_ofReal (by
      unfold FiniteCyclicDLP.Concrete.Amplification.attemptFloor
      positivity)] at floor
  rw [mul_comm] at floor
  have actual := underPersistent_eventWeight code supported (Layout.fieldWidth E)
    (FiniteCyclicDLP.orderWidth (problem I)) state (sampleInput base noQuantum I) event
  simp only [event, decide_eq_true_eq] at actual
  refine (floor.trans_eq actual.symm).trans ?_
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro record _
  exact selected_indicator_le _ _ _ (nativeECDLP_selected_sampleAccepted I _)

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
