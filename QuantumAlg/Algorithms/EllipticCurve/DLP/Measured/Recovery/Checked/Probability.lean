/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Checked
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Batch.Weight
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Input.Oracle.Empty
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Observation

/-!
# Actual selected exponent probability reaches the checked secret result

The original prescribed public input is supplied once, before the actual
quantum program. Its actual terminal measurements feed the full checked
recovery. The public point interpretation needed by recovery follows from
positive execution support, with no additional caller condition. The secret
remains a mathematical success witness and is never a runtime input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ScalarMultiplication.MeasuredPlacement
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Empty-service encodings retain the same complete actual execution. -/
private theorem initialExecution_supplied_empty (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    PublicInput.initialRunExecution E fieldTail odd problem points original =
      (PublicInput.exponentRun E fieldTail odd problem points).execute Reference
        (OracleInput.withEmptyService
          (PublicInput.initialInput E (orderWidth problem) problem original)).state := by
  have supplied : PublicInput.initialRunState E (orderWidth problem) problem original =
      (OracleInput.withEmptyService
        (PublicInput.initialInput E (orderWidth problem) problem original)).state := by
    dsimp only [PublicInput.initialRunState, OracleInput.withEmptyService]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  exact congrArg
    (fun incoming : State (PublicInput.before E (orderWidth problem)) Reference Unit =>
      (PublicInput.exponentRun E fieldTail odd problem points).execute Reference incoming) supplied

/-- Actual selected exponent probability reaches the original secret in the checked output. -/
theorem exponentCheckedRun_selected_probability_le (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (input : SecretInput problem) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    ((PublicInput.exponentRun E fieldTail odd problem points).outputDistribution
      (OracleInput.withEmptyService
        (PublicInput.initialInput E (orderWidth problem) problem original))).map
        (fun value => selectedExponentEvent problem input (QubitReadouts.mask value)) true ≤
      (exponentCheckedRun E fieldTail odd problem points nontrivial).outputDistribution
        (OracleInput.withEmptyService
          (PublicInput.initialInput E (orderWidth problem) problem original))
        (checkedSecretOutput problem input) := by
  rw [AlgorithmRun.outputDistribution_event_eq_effectWeight,
    AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  apply ENNReal.ofReal_le_ofReal
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let base := PublicInput.terminalBaseRef E (orderWidth problem)
  let target := PublicInput.terminalTargetRef E (orderWidth problem)
  let initial := OracleInput.withEmptyService
    (PublicInput.initialInput E (orderWidth problem) problem original)
  change _ ≤ (((BitWord.selectForCircuit
    (PublicInput.exponentRun E fieldTail odd problem points).code).seq
    (recoveryTail (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (fun _ : Fin 1 => rawRecoveryInput problem measured) base target)).execute Reference
        (initial.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))).effectWeight
      (fun entry => if entry.1.read
          (batchResultRead (PublicInput.terminal E (orderWidth problem))
            (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
              checkedSecretOutput problem input then
        Effect.one (Register.prod (checkedContext E problem).register Reference)
      else Effect.zero (Register.prod (checkedContext E problem).register Reference))
  let observed (stored : Store (checkedContext E problem)) :
      Effect (Register.prod (checkedContext E problem).register Reference) :=
    if stored.read (batchResultRead (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
        checkedSecretOutput problem input then Effect.one _ else Effect.zero _
  have actual := BitWord.selectForCircuit_seq_stored_effectWeight
    (PublicInput.exponentRun E fieldTail odd problem points).code
    (recoveryTail (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (fun _ : Fin 1 => rawRecoveryInput problem measured) base target)
    Reference (initial.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
    observed
  have supported : ∀ entry : (PublicInput.exponentRun E fieldTail odd problem points).Record,
      0 < (((PublicInput.exponentRun E fieldTail odd problem points).execute Reference
        initial.state).block entry).mass →
      ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read base) problem.generator.toMathlib ∧
      ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read target) problem.target.toMathlib := by
    intro entry positive
    have mass := congrArg
      (fun final : ExecutionState (PublicInput.exponentRun E fieldTail odd problem points).Record
          (Register.prod (PublicInput.terminal E (orderWidth problem)).register Reference) =>
        (final.block entry).mass)
      (initialExecution_supplied_empty E fieldTail odd problem points original)
    exact PublicInput.exponentRun_supported_represents E fieldTail odd
      problem points original entry (positive.trans_eq mass.symm)
  have bound := recoveryTail_selected_weight_le (p := p) (E := E)
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (ctx := PublicInput.terminal E (orderWidth problem)) (count := 1)
    (History := Store (PublicInput.before E (orderWidth problem)) ×
      (PublicInput.exponentRun E fieldTail odd problem points).code.Path)
    problem nontrivial input
    (fun _ : Fin 1 => measured) base target Reference
    ((PublicInput.exponentRun E fieldTail odd problem points).execute Reference initial.state)
    supported
  simp only [exists_const] at bound
  exact bound.trans_eq actual.symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
