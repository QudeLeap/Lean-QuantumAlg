/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Execution
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Retained.Semantics

/-!
# Actual measured-and-recovered output probability

The original exponent run feeds its actual retained finite results to the
actual complete raw recovery. The original selected-event probability is
bounded by the probability of the secret and true reconstruction flag read
from the new real retained result. This transfer uses the same complete
state blocks, with their original history and arbitrary external reference.
The original exceptional-input error is unchanged by the classical suffix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution FiniteCyclicDLP Canonical.Probability
open ScalarMultiplication.MeasuredPlacement.Allocation
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Mathematical success value observed in the original optional output shape. -/
def recoveredSecretOutput (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem) :
    CShape.Value (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.OutputShape (orderWidth problem)) :=
  .optionSome (.product (CShape.wordOfNat (orderWidth problem) input.secret.val) (.bit true))

private theorem retained_selected_weight_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (problem : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ problem.order)
    (input : SecretInput problem)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (key : StorageKey) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    state.effectWeight (fun entry =>
      if selectedExponentEvent problem input
          (QubitReadouts.mask (entry.1.read measured)) = true then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) ≤
      ((retainedCircuit (recoveryModulusSpec problem nontrivial)
        (rawRecoveryInput problem measured) key fresh).execute Reference state).effectWeight
        (fun entry => if entry.1.read (retainedRead ctx (orderWidth problem) key fresh) =
            recoveredSecretOutput problem input then
          Effect.one
            (Register.prod (retainedCtx ctx (orderWidth problem) key fresh).register Reference)
        else Effect.zero
          (Register.prod (retainedCtx ctx (orderWidth problem) key fresh).register Reference)) := by
  obtain ⟨record, equation, correct⟩ := retainedCircuit_actualRecord
    (recoveryModulusSpec problem nontrivial) (rawRecoveryInput problem measured) key fresh
  rw [equation Reference state]
  change _ ≤ (ExecutionState.mapClassical state
    (fun entry => ((record entry.1).1, entry.2, (record entry.1).2))).effectWeight
      (fun entry => if entry.1.read (retainedRead ctx (orderWidth problem) key fresh) =
          recoveredSecretOutput problem input then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference))
  rw [ExecutionState.effectWeight_mapClassical_decision]
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro entry _present
  by_cases selected :
      selectedExponentEvent problem input (QubitReadouts.mask (entry.1.read measured)) = true
  · obtain ⟨output, recovered, candidate, verified⟩ := outputOf_selectedExponentEvent_recovers
      problem input (QubitReadouts.mask (entry.1.read measured)) selected
      (recoveryModulusSpec problem nontrivial) rfl
    have written : (record entry.1).1.read (retainedRead ctx (orderWidth problem) key fresh) =
        recoveredSecretOutput problem input := by
      rw [correct entry.1, preparationInput_rawRecoveryInput, recovered]
      change ((entry.1.pushRetained key _ fresh).write (CWriteRef.retainedHead ctx key _ fresh)
        (encodedRawOutput _ (some output))).read
          (.storage (CWriteRef.retainedHead ctx key _ fresh).toCStorageRef) = _
      rw [Store.read_write_same]
      change CShape.Value.optionSome
        (.product (CShape.wordOfNat (orderWidth problem) output.candidate.val)
        (.bit output.verified)) = _
      rw [candidate, verified]
      rfl
    simp only [selected, written, if_true, le_refl]
  · simp only [selected, Bool.false_eq_true, if_false, Effect.weight_zero]
    split_ifs
    · simpa only [Effect.weight_one] using (state.block entry).mass_nonneg
    · simp only [Effect.weight_zero, le_refl]

/-- Actual classical recovery transfers the selected exponent probability to its stored secret. -/
theorem exponentRecoveryRun_selected_probability_le [Fact p.Prime]
    (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (input : SecretInput problem) {Reference : Register}
    (initial : Execution.Input (before p.size (2 * orderWidth problem)) Reference) :
    ((exponentRun E fieldTail odd problem points).outputDistribution initial).map
        (fun value => selectedExponentEvent problem input (QubitReadouts.mask value)) true ≤
      (exponentRecoveryRun E fieldTail odd problem points nontrivial).outputDistribution initial
        (recoveredSecretOutput problem input) := by
  rw [AlgorithmRun.outputDistribution_event_eq_effectWeight,
    AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  apply ENNReal.ofReal_le_ofReal
  change _ ≤ (((exponentRun E fieldTail odd problem points).code.seq
    (retainedCircuit (recoveryModulusSpec problem nontrivial)
      (rawRecoveryInput problem (QubitReadouts.input
        (exponentMeasurementCells p (orderWidth problem))))
      (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey
      (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey_fresh)).execute
      Reference
        (initial.state.mapClassical (fun store => (store, store)))).effectWeight
          (fun entry => if entry.1.read
              (retainedRead (exponentMeasurementContext p (orderWidth problem))
                (orderWidth problem)
                (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey
                (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey_fresh) =
              recoveredSecretOutput problem input then
            Effect.one (Register.prod
              (retainedCtx (exponentMeasurementContext p (orderWidth problem))
                (orderWidth problem)
                (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey
                (exponentMeasurementContext p
                  (orderWidth problem)).canonicalFreshKey_fresh).register
              Reference)
          else Effect.zero (Register.prod
            (retainedCtx (exponentMeasurementContext p (orderWidth problem))
              (orderWidth problem)
              (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey
              (exponentMeasurementContext p (orderWidth problem)).canonicalFreshKey_fresh).register
            Reference))
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]
  exact retained_selected_weight_le problem nontrivial input
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem))) _ _ Reference
    ((exponentRun E fieldTail odd problem points).execute Reference initial.state)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
