/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Checked
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Batch.Weight
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Points
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect

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

/-- Actual selected exponent probability reaches the original secret in the checked output. -/
theorem exponentCheckedRun_selected_probability_le (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (input : SecretInput problem) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    ((PublicInput.exponentRun E fieldTail odd problem points).outputDistribution
      (PublicInput.initialInput E (orderWidth problem) problem original)).map
        (fun value => selectedExponentEvent problem input (QubitReadouts.mask value)) true ≤
      (exponentCheckedRun E fieldTail odd problem points nontrivial).outputDistribution
        (PublicInput.initialInput E (orderWidth problem) problem original)
        (checkedSecretOutput problem input) := by
  rw [AlgorithmRun.outputDistribution_event_eq_effectWeight,
    AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  apply ENNReal.ofReal_le_ofReal
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let base := PublicInput.terminalBaseRef E (orderWidth problem)
  let target := PublicInput.terminalTargetRef E (orderWidth problem)
  let initial := PublicInput.initialInput E (orderWidth problem) problem original
  change _ ≤ (((PublicInput.exponentRun E fieldTail odd problem points).code.seq
    (recoveryTail (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      (fun _ : Fin 1 => rawRecoveryInput problem measured) base target)).execute Reference
        (initial.state.mapClassical (fun store => (store, store)))).effectWeight
      (fun entry => if entry.1.read
          (batchResultRead (PublicInput.terminal E (orderWidth problem))
            (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
              checkedSecretOutput problem input then
        Effect.one (Register.prod (checkedContext E problem).register Reference)
      else Effect.zero (Register.prod (checkedContext E problem).register Reference))
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]
  have bound := recoveryTail_selected_weight_le problem nontrivial input
    (fun _ : Fin 1 => measured) base target Reference
    ((PublicInput.exponentRun E fieldTail odd problem points).execute Reference initial.state)
    (fun entry positive => PublicInput.exponentRun_supported_represents E fieldTail odd
      problem points original entry positive)
  simp only [exists_const] at bound
  exact bound

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
