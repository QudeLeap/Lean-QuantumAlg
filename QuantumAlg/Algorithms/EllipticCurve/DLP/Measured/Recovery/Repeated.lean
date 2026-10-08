/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Checked
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Store
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling

/-!
# Actual finite measured ECDLP with complete workspace reuse

Original arithmetic and terminal storage are allocated once. Each round
really resets and seeds all existing quantum wires, executes the original
sampling and Z readout, and immediately runs complete checked recovery on
those stored results. The original seven first-success destinations are
retained once; only the final optional result is packed after the loop.

The seed is fixed before execution. Neither the number of rounds nor an
intermediate result changes the set of resident quantum wires. Probability
amplification and resource bounds are separate proofs about this actual code.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual round resets the original full basis before the unchanged sampling and readout. -/
def samplingRound (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)) :=
  (samplingReset E fieldTail (orderWidth problem) sameWidth fits seed).seq
    (samplingReadout E fieldTail odd problem points)

/-- Preparation, original gates and readout reuse the same complete terminal context. -/
theorem samplingRound_isLocal (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).IsLocal :=
  ⟨samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed,
    samplingReadout_isLocal E fieldTail odd problem points⟩

/-- The actual reset, sampling and readout round has the selected model's
complete execution state, with only its finite path history relabeled. -/
theorem samplingRound_selected_execute (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (Reference : Register) {H : Type} [Fintype H]
    (state : State (PublicInput.terminal E (orderWidth problem)) Reference
      ((.quantum AlgorithmGate.model .empty : ExecutionModel).HiddenState × H)) :
    (BitWord.selectForCircuit
      (samplingRound E fieldTail sameWidth fits odd problem points seed)).execute
        Reference state =
      ((samplingRound E fieldTail sameWidth fits odd problem points seed).execute
        Reference state).mapHistory (fun record =>
          (record.1, (record.2.1,
            BitWord.selectForCircuitPathEquiv
              (samplingRound E fieldTail sameWidth fits odd problem points seed)
                record.2.2))) := by
  exact BitWord.selectForCircuit_execute _ Reference state

/-- The original preparation and terminal allocation occur once before all sampled rounds. -/
def exponentRepeatedInitial (problem : KnownOrderProblem E.GroupPoint) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (PublicInput.before E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)) :=
  (PublicInput.initializeWork E (orderWidth problem)).seq
    (PublicInput.allocateTerminal E (orderWidth problem))

omit [Fact p.Prime] in
/-- One original initialization transports its full output state into the
bit/word model used by the real repeated recovery circuit. -/
theorem exponentRepeatedInitial_selected_execute
    (problem : KnownOrderProblem E.GroupPoint) (Reference : Register)
    {H : Type} [Fintype H]
    (state : State (PublicInput.before E (orderWidth problem)) Reference
      ((.quantum AlgorithmGate.model .empty : ExecutionModel).HiddenState × H)) :
    (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).execute
        Reference state =
      ((exponentRepeatedInitial E problem).execute Reference state).mapHistory
        (fun record => (record.1, (record.2.1,
          BitWord.selectForCircuitPathEquiv (exponentRepeatedInitial E problem)
            record.2.2))) := by
  exact BitWord.selectForCircuit_execute _ Reference state

/-- The actual selected-model checked recovery runs after each original round. -/
def repeatedTailRun (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) (count : Nat) :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem)) (checkedContext E problem)
      (.option (.unsignedWord (orderWidth problem))) :=
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let round := BitWord.selectForCircuit
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
  sampledRecoveryRun round
    (BitWord.selectForCircuit_isLocal _
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)) count
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))

/-- The complete actual repeated execution separates one initialization from its checked loop. -/
def exponentRepeatedCode (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) (count : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (checkedContext E problem) :=
  (BitWord.selectForCircuit (exponentRepeatedInitial E problem)).seq
    (repeatedTailRun E fieldTail sameWidth fits odd problem points seed nontrivial count).code

/-- Finite actual sampling and checked recovery retain one workspace and one final result. -/
def exponentRepeatedRun (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) (count : Nat) :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (checkedContext E problem)
      (.option (.unsignedWord (orderWidth problem))) where
  code := exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
    nontrivial count
  output := (repeatedTailRun E fieldTail sameWidth fits odd problem points seed
    nontrivial count).output

/-- Supply the unique empty classical service state with the prescribed public input. -/
def repeatedOracleInput (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference :=
  OracleInput.ofKernel (PublicInput.initialInput E (orderWidth problem) problem original)
    (fun _ => PMF.pure ())

local instance {α : Type} : DecidableEq α := Classical.decEq α

omit [Fact p.Prime] in
/-- The empty service has one deterministic state while retaining every input block. -/
theorem repeatedOracleInput_state
    (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    (repeatedOracleInput E problem original).state =
      (PublicInput.initialInput E (orderWidth problem) problem original).state.mapClassical
        (fun value => (value, ())) := by
  exact (kernelChoice_pure
    (PublicInput.initialInput E (orderWidth problem) problem original).state
    (fun _ => ())).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)

omit [Fact p.Prime] in
/-- The actual empty-service input becomes the prescribed persistent proof state. -/
theorem repeatedOracleInput_persistentInitialState
    (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference) :
    ((repeatedOracleInput E problem original).state.mapClassical
      (fun value => (value.1, (value.2, value.1)))) =
      PublicInput.persistentInitialState E (orderWidth problem) problem original := by
  rw [repeatedOracleInput_state]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ (by funext value; rfl)

omit [Fact p.Prime] in
/-- Any actual run uses the prescribed persistent state after recording its input history. -/
theorem repeatedRun_execute_persistentInitialState
    (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    {post : RuntimeCtx .quantum} {outputShape : CShape}
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) post outputShape) :
    run.execute Reference (repeatedOracleInput E problem original).state =
      run.code.execute Reference
        (PublicInput.persistentInitialState E (orderWidth problem) problem original) := by
  unfold AlgorithmRun.execute
  exact congrArg (run.code.execute Reference)
    (repeatedOracleInput_persistentInitialState E problem original)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
