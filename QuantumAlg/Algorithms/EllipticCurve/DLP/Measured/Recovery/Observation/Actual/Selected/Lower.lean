/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Seed.GoodEffectAgreement
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.ReferenceEvent
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.History.Reference
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Semantics
import all QuantumAlg.Core.Execution.Classical.Branch

/-!
# The actual streaming selected-event floor on arbitrary mixed input

Every complete original Store remains a separate spectral mixture. The
uniform pure Reference lower bound therefore lifts with its own original
nonnegative spectral weights. Summing all actual reset fibers recovers the
incoming total mass, including zero, without dividing or conditioning.
No old physical execution or structural compiler supplies this bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualSelectedLower

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (State Store)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

set_option maxHeartbeats 400000 in
-- Summing every complete reset Store fiber needs a finite local elaboration budget.
/-- The complete actual reset Store fibers retain exactly the incoming total mass. -/
lemma resetStore_total_mass (fieldTail m : Nat) (seed : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (∑ original : Store (Recovery.Layout.terminal p.size m),
      (Recovery.Initialization.HistoryReference.selectedStoreDensity (environment := environment)
        E fieldTail m seed
        state (fun _ => True) original).mass) = state.mass := by
  let reset := (Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
    state
  have kept : @ExecutionState.filterClassical _ _ _ reset (fun _ => True)
      (fun _ => Classical.propDecidable True) = reset := by
    apply ExecutionState.ext
    intro record
    simp only [ExecutionState.filterClassical_block, if_true]
  simp only [Recovery.Initialization.HistoryReference.selectedStoreDensity,
    ExecutionState.quantumMarginal_mass]
  erw [kept]
  exact (ExecutionState.sum_selectClassical_mass reset Prod.fst).trans
    (Circuit.execute_mass (Recovery.Initialization.newReset E fieldTail m seed) environment
      Reference state)

open _root_.QuantumAlg.FiniteCyclicDLP
  (KnownOrderProblem orderWidth fourierModulus order_le_fourierModulus)
open _root_.QuantumAlg.FiniteCyclicDLP.Canonical.Probability (SecretInput)
open GenericPointAddition.InPlace.Semantics (radixUnit)
open Recovery.Conversion (convertedStages)
open ECDLP.Measured (preparedExceptionalMass)

/-- The literal actual raw-bit event keeps the original floor on any dirty mixed input. -/
lemma actual_selected_event_lower (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (seed : AffinePoint E)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (odd : Odd p) (input : SecretInput problem)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((convertedStages (m := orderWidth problem) E problem.order points
        (Recovery.Layout.order (orderWidth problem))
        (radixUnit p fieldTail.succ odd)).execute environment Reference
          ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
            environment Reference state)).effectWeight
              (fun record =>
                if ECDLP.Measured.selectedExponentEvent problem input
                    (ActualFrequencyEvent.resultBits p.size (orderWidth problem) record.1) = true
                then Effect.one ((Recovery.Layout.terminal p.size (orderWidth
                  problem)).register.prod
                  Reference)
                else Effect.zero ((Recovery.Layout.terminal p.size (orderWidth
                  problem)).register.prod
                  Reference)) := by
  have bound := ActualReferenceEvent.actual_event_weight_ge_selected_mass (environment :=
    environment)
    (m := orderWidth problem) E fieldTail seed
    problem.order points (radixUnit p fieldTail.succ odd) state (fun _ => True)
    (fun final => ECDLP.Measured.selectedExponentEvent problem input
      (ActualFrequencyEvent.resultBits p.size (orderWidth problem) final) = true)
    problem.order_pos (order_le_fourierModulus problem)
    ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed))
    (fun original reference => SeedGoodEffectAgreement.referenceComponent_selected_lower E
      problem fieldTail seed points addends odd input original reference)
  rw [resetStore_total_mass] at bound
  simpa only [true_and] using bound

end

end ActualSelectedLower
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
