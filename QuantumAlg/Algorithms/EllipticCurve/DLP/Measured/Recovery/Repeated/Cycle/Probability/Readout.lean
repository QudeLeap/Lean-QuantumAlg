/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Seeded
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Probability.Persistent

/-!
# The actual reused ECC readout on its admitted seeded input

The independent initialized bank gives basis support even with arbitrary
reference correlations. The unchanged readout runs beside all seven retained
classical cells; its selected exponent event is contained in the real
checked-recovery candidate event. No extra reset appears in this code.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (predicate : Prop) : Decidable predicate := Classical.propDecidable predicate

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The actual candidate event in the seven persistent cells, independent
of the sampling code that produced the measured exponent word. -/
def persistentReadoutCandidateEffects
    {Reference : Register} {History : Type} :
    Circuit.EffectFamily
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference History := by
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  exact fun record =>
    if SampleAccepted (Canonical.Layout.curveSpec E)
        (recoveryModulusSpec problem nontrivial)
        problem.generator.toMathlib problem.target.toMathlib
        (record.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (rawRecoveryInput problem measured))) then
      Effect.one ((persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)
    else Effect.zero ((persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).register.prod Reference)

/-- The source floor on the named readout's candidate event for any actual
subnormalized state, including a selected failure fiber. -/
def SupportedReadoutCandidateFloor
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H)) : Prop :=
  state.mass * ((problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed)) ≤
    ((persistentSamplingReadout E fieldTail odd problem points).execute Reference
      state).effectWeight
      (persistentReadoutCandidateEffects E problem nontrivial)

/-- The admitted input specialization keeps the section contract's large
candidate event separate from its circuit application. -/
def SeededReadoutCandidateFloor
    {Reference : Register}
    (supplied : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) : Prop :=
  SupportedReadoutCandidateFloor E fieldTail odd problem points seed nontrivial
    (State.skip supplied.state)

/-- The unchanged reused readout has the corrected candidate floor on every
actual state with the prescribed sampling-basis support. -/
theorem persistentSamplingReadout_candidate_weight_of_support
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (witness : SecretInput problem)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference
        (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ basis, basis.1 ≠
      samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed →
        state.quantumMarginal.matrix basis basis = 0) :
    SupportedReadoutCandidateFloor E fieldTail odd problem points seed nontrivial state := by
  unfold SupportedReadoutCandidateFloor
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let code := samplingReadout E fieldTail odd problem points
  have supported := samplingReadout_isLocal E fieldTail odd problem points
  let selectedCode := BitWord.selectForCircuit code
  have selectedSupported : selectedCode.IsLocal :=
    BitWord.selectForCircuit_isLocal code supported
  let localReference := persistentLocalReference
    (PublicInput.terminal E (orderWidth problem)) (Canonical.Layout.fieldWidth E)
    (orderWidth problem) Reference
  let split := underPersistentSplitState (Canonical.Layout.fieldWidth E)
    (orderWidth problem) state
  have original := selectedSamplingReadout_weight_bound E fieldTail sameWidth fits odd
    problem points seed addends witness split
    (underPersistentSplitState_basisSupport (Canonical.Layout.fieldWidth E)
      (orderWidth problem) state
      (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed)
      support)
  rw [underPersistentSplitState_mass] at original
  have sameWeight :
      (selectedCode.execute localReference split).effectWeight
        (samplingSelectedEffects E problem witness localReference) =
      (code.execute localReference split).effectWeight
        (samplingSelectedEffects E problem witness localReference) := by
    rw [BitWord.selectForCircuit_execute code localReference split]
    rw [State.effectWeight_mapHistory]
    rfl
  have actual := underPersistent_eventWeight selectedCode selectedSupported
    (Canonical.Layout.fieldWidth E) (orderWidth problem) state measured
    (fun value => selectedExponentEvent problem witness (QubitReadouts.mask value))
  change _ = (selectedCode.execute _ split).effectWeight
    (samplingSelectedEffects E problem witness _) at actual
  rw [sameWeight] at actual
  have inclusion := selectedPersistentSample_weight_le
    (ctx := PublicInput.terminal E (orderWidth problem)) problem nontrivial witness
    (Canonical.Layout.fieldWidth E) measured
    ((underPersistent selectedCode selectedSupported (Canonical.Layout.fieldWidth E)
      (orderWidth problem)).execute Reference state)
  have sameCode :
      underPersistent selectedCode selectedSupported (Canonical.Layout.fieldWidth E)
        (orderWidth problem) =
      persistentSamplingReadout E fieldTail odd problem points := rfl
  have selectedMass := original.trans_eq actual.symm
  rw [sameCode] at selectedMass inclusion
  exact selectedMass.trans
    (by simpa only [persistentReadoutCandidateEffects, measured] using inclusion)

/-- Every admitted seeded input satisfies the same candidate floor without
an added reset in the reused circuit. -/
theorem persistentSamplingReadout_candidate_weight_on_seededInput
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (witness : SecretInput problem)
    {Reference : Register}
    (supplied : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      supplied.localState) :
    SeededReadoutCandidateFloor E fieldTail odd problem points seed nontrivial supplied := by
  unfold SeededReadoutCandidateFloor
  apply persistentSamplingReadout_candidate_weight_of_support E fieldTail sameWidth fits odd
    problem points seed nontrivial addends witness (State.skip supplied.state)
  intro basis outside
  rw [State.skip_quantumMarginal]
  exact checkedSectionSeededInitialization_jointSupport E fieldTail sameWidth fits
    problem seed supplied seeded basis outside

/-- The source-scoped known-order problem supplies the mathematical witness
internally; the real reused readout contract needs no extra caller input. -/
theorem persistentSamplingReadout_candidate_weight_from_knownOrder
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (supplied : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed
      supplied.localState) :
    SeededReadoutCandidateFloor E fieldTail odd problem points seed nontrivial supplied :=
  persistentSamplingReadout_candidate_weight_on_seededInput E fieldTail sameWidth fits odd
    problem points seed nontrivial addends (SecretInput.ofKnownOrderProblem problem)
    supplied seeded

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
