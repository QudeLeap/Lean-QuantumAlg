/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding

/-!
# Actual streaming candidate mass beside all persistent recovery cells

The existing paid packing input and the selected observation read the same
physical cells, reversing positions only inside the two final output blocks.
Selecting the bit/word execution model changes only the recorded path. The
complete seven-cell embedding retains every stored value and arbitrary
Reference correlation before applying the source-derived one-round floor.

The original selected-family inclusion then gives the actual native candidate
mass floor for the exact sampling round used by StreamingRecovery.run. No
point representation, initialized latch, clean bank, normalized state or
independent-sampling premise is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.CandidateProbability

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ECDLP.Measured
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth fourierModulus)
open _root_.QuantumAlg.FiniteCyclicDLP.Canonical.Probability (SecretInput)
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The paid decoder reverses precisely the final observation's two physical blocks. -/
lemma paid_reversePosition_eq_blockReverse (m : Nat) (index : Fin (2 * m)) :
    PaidPacking.reversePosition m index = TerminalStoreCoordinates.blockReverse m index := rfl

private def persistentSplitInput {ctx : RuntimeCtx .quantum} (width scalarWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Unit × History)) :
    State ctx ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference)
      (Unit × (Store (persistentEmbedding ctx width scalarWidth).frame × History)) :=
  ((persistentEmbedding ctx width scalarWidth).split state).mapClassical (fun record =>
    (record.1, (record.2.2.1, (record.2.1, record.2.2.2))))

private lemma persistentSplitInput_mass {ctx : RuntimeCtx .quantum} (width scalarWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Unit × History)) :
    (persistentSplitInput width scalarWidth state).mass = state.mass := by
  unfold persistentSplitInput
  rw [ExecutionState.mapClassical_mass, ContextEmbedding.contextEmbedding_split_mass]

set_option maxHeartbeats 400000 in
-- The complete persistent-frame observation exceeded the default proof budget.
private lemma persistentJoin_eventWeight {ctx : RuntimeCtx .quantum} (width scalarWidth : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference)
      (Store (persistentEmbedding ctx width scalarWidth).frame × History))
    {shape : CShape} (input : CInputRef ctx shape) (event : shape.Value → Bool) :
    ((persistentEmbedding ctx width scalarWidth).join state).effectWeight (fun record =>
      if event (record.1.read (persistentInput width scalarWidth input)) = true then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      state.effectWeight (fun record => if event (record.1.read input) = true then
        Effect.one (ctx.register.prod
          ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))
      else Effect.zero (ctx.register.prod
        ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))) := by
  have observation := Recovery.PublicInput.Probability.indicator_join
    (persistentEmbedding ctx width scalarWidth) state (fun record =>
      event (record.1.read (persistentInput width scalarWidth input)) = true)
  conv at observation =>
    lhs
    arg 2
    equals (fun record : Store (persistentCtx ctx width scalarWidth) × History =>
      if event (record.1.read (persistentInput width scalarWidth input)) = true then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =>
      funext record
      by_cases accepted : event (record.1.read (persistentInput width scalarWidth input)) = true
      · simp only [if_pos accepted]
      · simp only [if_neg accepted]
  conv at observation =>
    rhs
    arg 2
    equals (fun record : Store ctx ×
      (Store (persistentEmbedding ctx width scalarWidth).frame × History) =>
        if event (record.1.read input) = true then
          Effect.one (ctx.register.prod
            ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))
        else Effect.zero (ctx.register.prod
          ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))) =>
      funext record
      have reads :
          (((persistentEmbedding ctx width scalarWidth).record History).symm record).1.read
            (persistentInput width scalarWidth input) = record.1.read input := by
        change ((persistentEmbedding ctx width scalarWidth).store.symm
          (record.1, record.2.1)).read (persistentInput width scalarWidth input) = _
        rw [← candidateCheck_persistentEmbedding_input]
        exact (persistentEmbedding ctx width scalarWidth).contextEmbedding_input_read
          record.1 record.2.1 input
      by_cases accepted : event (record.1.read input) = true
      · simp only [reads, if_pos accepted]
      · simp only [reads, if_neg accepted]
  exact observation

set_option maxHeartbeats 800000 in
-- Checking the complete split/execute/join proof exceeded the previous finite budget.
private lemma sampleUnderPersistent_eventWeight
    {ctx : RuntimeCtx .quantum}
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model) ctx ctx false)
    (width scalarWidth : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference (Unit × History))
    {shape : CShape} (input : CInputRef ctx shape) (event : shape.Value → Bool) :
    ((sampleUnderPersistent code width scalarWidth).execute environment Reference
      state).effectWeight
      (fun record => if event (record.1.read (persistentInput width scalarWidth input)) = true then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      (code.execute environment ((persistentEmbedding ctx width scalarWidth).frame.register.prod
        Reference)
        (persistentSplitInput width scalarWidth state)).effectWeight (fun record =>
          if event (record.1.read input) = true then
            Effect.one (ctx.register.prod
              ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))
          else Effect.zero (ctx.register.prod
            ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))) := by
  have executed := candidateCheck_sampleUnderPersistent_execute (environment := environment)
    code width scalarWidth Reference state
  let child := code.execute environment ((persistentEmbedding ctx width
    scalarWidth).frame.register.prod Reference)
    (persistentSplitInput width scalarWidth state)
  let update :
      (Store ctx × (Unit ×
        ((Store (persistentEmbedding ctx width scalarWidth).frame × History) × code.Path))) →
      (Store ctx ×
        (Store (persistentEmbedding ctx width scalarWidth).frame ×
          (Unit × (History × code.Path)))) :=
    fun record => (record.1, (record.2.2.1.1,
      (record.2.1, (record.2.2.1.2, record.2.2.2))))
  let effects :
      (Store ctx × (Store (persistentEmbedding ctx width scalarWidth).frame ×
        (Unit × (History × code.Path)))) →
      Effect (ctx.register.prod
        ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference)) :=
    fun record => if event (record.1.read input) = true then
      Effect.one (ctx.register.prod
        ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))
    else Effect.zero (ctx.register.prod
      ((persistentEmbedding ctx width scalarWidth).frame.register.prod Reference))
  have arranged : (sampleUnderPersistent code width scalarWidth).execute environment Reference
    state =
      (persistentEmbedding ctx width scalarWidth).join (child.mapClassical update) := by
    refine executed.trans ?_
    dsimp only [child, update, persistentSplitInput]
    apply congrArg (persistentEmbedding ctx width scalarWidth).join
    apply Circuit.pushforward_congr
    apply congrArg (code.execute environment ((persistentEmbedding ctx width
      scalarWidth).frame.register.prod Reference))
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  refine (congrArg (fun output : State (persistentCtx ctx width scalarWidth) Reference
      (Unit × (History × code.Path)) => output.effectWeight (fun record =>
        if event (record.1.read (persistentInput width scalarWidth input)) = true then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)))
    arranged).trans ?_
  have mapweight := ExecutionState.effectWeight_mapClassical_decision
    inferInstance child update effects
  have joined := persistentJoin_eventWeight (ctx := ctx) width scalarWidth
    (Reference := Reference) (History := Unit × (History × code.Path))
    (child.mapClassical update) input event
  conv at joined =>
    rhs
    rw [mapweight]
  exact joined

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

omit [Fact p.Prime] in
/-- The actual paid caller input equals the observation input at the actual field width. -/
lemma paid_callerInput_eq_observation :
    PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)) =
      (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)).input
        (Recovery.PublicInput.Probability.readoutInput (p := p) (orderWidth problem)) := by
  unfold PaidPacking.callerInput PaidPacking.input Recovery.PublicInput.Probability.readoutInput
  apply congrArg (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)).input
  change CInputRef.fixedVector _ = CInputRef.fixedVector _
  apply congrArg CInputRef.fixedVector
  funext index
  change CInputRef.storage _ = CInputRef.storage _
  rw [paid_reversePosition_eq_blockReverse]

omit [Fact p.Prime] in
/-- The original recovery adapter is the run's exact same-width structural read. -/
lemma actual_recoveryInput_eq_rawRecoveryInput {ctx : RuntimeCtx .quantum}
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2))) :
    recoveryInput (orderWidth problem) measured = rawRecoveryInput problem measured := rfl

omit [Fact p.Prime] in
/-- The actual run and the selected-family inclusion use the same public-order modulus. -/
lemma actual_modulus_eq_recoveryModulus (nontrivial : 2 ≤ problem.order) :
    FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial =
      recoveryModulusSpec problem nontrivial := rfl

set_option maxHeartbeats 400000 in
-- The complete selected circuit's history transport exceeds the default proof budget.
/-- Selecting bit/word operations preserves the actual public round's selected mass. -/
lemma actual_round_selected_weight {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference (Unit × History))
    (input : SecretInput problem) :
    ((round E fieldTail problem points seed problem.order
      (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute environment
        Reference
        state).effectWeight
        (Recovery.PublicInput.Probability.selectedEffects E problem input Reference) =
      ((Circuit.embed (allowAllocation := false)
        (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
        (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem) seed problem.order
          points
          (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))).execute
            ⟨environment.quantum, environment.classical⟩ Reference state).effectWeight
            (Recovery.PublicInput.Probability.selectedEffects E problem input Reference) := by
  rw [round, BitWord.selectForCircuit_execute]
  rw [State.effectWeight_mapHistory]
  rfl

/-- The exact streaming round retains the source-derived selected-family floor. -/
lemma actual_round_selected_readout_bound
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.PublicInput.context E (orderWidth problem)) Reference (Unit × History))
    (input : SecretInput problem) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((round E fieldTail problem points seed problem.order
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)).execute
          environment Reference
          state).effectWeight
          (Recovery.PublicInput.Probability.selectedEffects E problem input Reference) := by
  exact (Recovery.PublicInput.Probability.actual_embedded_sampling_selected_readout_bound
    (environment := ⟨environment.quantum, environment.classical⟩) E
    fieldTail odd
    seed problem points sameWidth fits addends state input).trans_eq
      (actual_round_selected_weight E fieldTail odd problem points seed state input).symm

set_option maxHeartbeats 800000 in
-- Checking the complete persistent-context probability proof exceeded the previous finite budget.
/-- Every actual failure fiber has the original complete native candidate mass floor. -/
lemma actual_persistent_round_candidate_weight_bound
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register} {History : Type} [Fintype History]
    (state : State (persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference (Unit × History)) :
    state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
      ((sampleUnderPersistent (round E fieldTail problem points seed problem.order
        (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd))
          (ECDLP.Canonical.Layout.fieldWidth E)
          (orderWidth problem)).execute environment Reference state).effectWeight (fun record =>
            if SampleAccepted (ECDLP.Canonical.Layout.curveSpec E)
                (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
                problem.generator.toMathlib problem.target.toMathlib
                (record.1.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E)
                  (orderWidth problem) (recoveryInput (orderWidth problem)
                    (PaidPacking.callerInput
                      (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))))))
                        then
              Effect.one ((persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
                (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)
            else Effect.zero ((persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
              (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod
                Reference)) := by
  let measured := PaidPacking.callerInput
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
  let code := round E fieldTail problem points seed problem.order
    (GenericPointAddition.InPlace.Semantics.radixUnit p fieldTail.succ odd)
  have original := actual_round_selected_readout_bound (environment := environment) E fieldTail
    odd problem points seed
    sameWidth fits addends
    (persistentSplitInput (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) state) input
  rw [persistentSplitInput_mass] at original
  have actual := sampleUnderPersistent_eventWeight (environment := environment) code
    (ECDLP.Canonical.Layout.fieldWidth E)
    (orderWidth problem) state measured
    (fun value => selectedExponentEvent problem input (QubitReadouts.mask value))
  have selectedSame (K : Type) :
      (fun record : Store (Recovery.PublicInput.context E (orderWidth problem)) × K =>
        if selectedExponentEvent problem input
          (QubitReadouts.mask (record.1.read measured)) = true then
          Effect.one ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
            ((persistentEmbedding (Recovery.PublicInput.context E (orderWidth problem))
              (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).frame.register.prod
                Reference))
        else Effect.zero ((Recovery.PublicInput.context E (orderWidth problem)).register.prod
          ((persistentEmbedding (Recovery.PublicInput.context E (orderWidth problem))
            (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).frame.register.prod
              Reference))) =
        Recovery.PublicInput.Probability.selectedEffects E problem input
          ((persistentEmbedding (Recovery.PublicInput.context E (orderWidth problem))
            (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)).frame.register.prod
              Reference) (OutputHistory := K) := by
    funext record
    dsimp only [measured, Recovery.PublicInput.Probability.selectedEffects,
      Recovery.PublicInput.Probability.publicReadoutBits]
    simp only [paid_callerInput_eq_observation]
    by_cases accepted : selectedExponentEvent problem input
      (QubitReadouts.mask (record.1.read
        ((Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)).input
          (Recovery.PublicInput.Probability.readoutInput (p := p) (orderWidth problem))))) = true
    · erw [if_pos accepted]
    · erw [if_neg accepted]
  conv at actual =>
    rhs
    arg 2
    rw [selectedSame]
  let sampled := Circuit.execute (model := .quantum AlgorithmGate.model .empty
    BitWord.model)
    (pre := persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))
    (post := persistentCtx (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))
    (allowAllocation := true) (H := History)
    (sampleUnderPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (ctx := Recovery.PublicInput.context E (orderWidth problem))
      code (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)) environment Reference state
  have inclusion := selectedPersistentSample_weight_le (p := p) (E := E) (kind := .quantum)
    (ctx := Recovery.PublicInput.context E (orderWidth problem)) (Reference := Reference)
    problem nontrivial input (ECDLP.Canonical.Layout.fieldWidth E) measured sampled
  rw [← actual_modulus_eq_recoveryModulus E problem nontrivial,
    ← actual_recoveryInput_eq_rawRecoveryInput E problem] at inclusion
  exact (original.trans_eq actual.symm).trans inclusion

end

end ExecutionContract.CandidateProbability
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
