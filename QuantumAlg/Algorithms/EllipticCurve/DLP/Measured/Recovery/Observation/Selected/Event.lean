/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.Selected.Lower
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Terminal.StoreCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract

/-!
# Actual streaming selected-frequency observation and its original floor

The structural read consumes existing result cells. Its selected effect and
source-derived lower bound refer to the actual reset and converted execution
on every complete Store, dirty subnormalized input and arbitrary Reference.
No old terminal execution or common-terminal comparison is used by these
three declarations. Their original mathematical predicates, calibration and
caller parameters are retained. Other imported implementation owners still
require their separate compiler-dependency migration.

The independent full old/new observation theorem remains in SelectedObservation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace SelectedObservation

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.FiniteCyclicDLP ECDLP.Measured

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Original paired big-endian bits are read structurally from corresponding final result cells. -/
def readoutBits (modulus m : Nat) (stored : Store (Recovery.Layout.terminal modulus.size m))
    (index : Fin (2 * m)) : Bool :=
  decide ((stored.read (.storage (Recovery.Layout.resultCell modulus.size m
    (TerminalStoreCoordinates.blockReverse m index)).toCStorageRef)).toFin.val = 1)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (odd : Odd p) (seed : AffinePoint E)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E)
  (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)

variable {Reference : Register} {History : Type} [Fintype History]
  (state : State (Recovery.Layout.terminal p.size (orderWidth problem)) Reference
    (ClassicalOracleModel.empty.HiddenState × History))

/-- The mathematical selected event reads actual existing result cells of the streaming caller. -/
def selectedEffects
    (input : _root_.QuantumAlg.FiniteCyclicDLP.Canonical.Probability.SecretInput problem)
    (Reference : Register) {OutputHistory : Type} :
    Circuit.EffectFamily (Recovery.Layout.terminal p.size (orderWidth problem)) Reference
      OutputHistory :=
  fun record => if selectedExponentEvent problem input
    (readoutBits p (orderWidth problem) record.1) = true then
      Effect.one ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod Reference)
    else Effect.zero ((Recovery.Layout.terminal p.size (orderWidth problem)).register.prod
      Reference)

set_option maxHeartbeats 400000 in
-- The complete selected-event bound needs a finite local elaboration budget.
/-- The actual mixed selected event attains the original floor directly from its legal kernel. -/
lemma actual_reset_converted_selected_readout_bound
    (E : PrimeFieldShortWeierstrass p)
    (fieldTail : Nat) (odd : Odd p) (seed : AffinePoint E)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (_sameWidth : fieldTail.succ = p.size) (_fits : p < 2 ^ fieldTail.succ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size (orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : _root_.QuantumAlg.FiniteCyclicDLP.Canonical.Probability.SecretInput problem) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((Recovery.Conversion.convertedStages E problem.order points
        (Recovery.Layout.order (orderWidth problem))
          (GenericPointAddition.InPlace.Semantics.radixUnit p
          fieldTail.succ odd)).execute environment Reference
            ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).execute
              environment Reference state)).effectWeight (selectedEffects E problem input
              Reference) := by
  refine (ActualSelectedLower.actual_selected_event_lower (environment := environment) E problem
    fieldTail seed points addends odd input state).trans_eq ?_
  apply congrArg
  funext record
  rfl

end

end SelectedObservation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
