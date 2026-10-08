/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Validity
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Initialization

/-!
# Actual repeated ECDLP never returns a wrong secret

The original public points enter through the prescribed borrowed input and
remain valid on every actual prefix. Real persistent allocation supplies
false acceptance and the zero selected word. The actual sampling loop keeps
the original range and checked point equation; the final actual option pack
therefore returns only the original unique secret. No intermediate support,
zero, inverse, candidate-correctness or sampling-independence promise is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem storeSupported_execute_mapHistory {model : ExecutionModel}
    {origin result : RuntimeCtx model.kind}
    (code : Circuit model origin result) {Reference : Register}
    {H K : Type} [Fintype H] [Fintype K]
    (state : State origin Reference (model.HiddenState × H)) (update : H → K)
    (predicate : Store result → Prop) :
    storeSupported (code.execute Reference
      (state.mapHistory (fun record => (record.1, update record.2)))) predicate ↔
      storeSupported (code.execute Reference state) predicate := by
  rw [Circuit.execute_mapHistory, storeSupported_mapHistory]

private theorem retainPersistent_initialized_invariant {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind}
    (setup : Circuit model origin ctx) (width scalarWidth order : Nat)
    (positiveOrder : 0 < order)
    (consequence : Store (persistentCtx ctx width scalarWidth) → Prop)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference (model.HiddenState × H)) :
    storeSupported ((setup.seq (retainPersistent ctx width scalarWidth)).execute
        Reference initial)
      (fun store =>
        (store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
          order ∧
        ((store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true → consequence store)) := by
  apply (storeSupported_seq setup (retainPersistent ctx width scalarWidth) initial
    (fun store =>
      (store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        order ∧
      ((store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true → consequence store))).mpr
  intro entry present
  have values := retainPersistent_latches_supported width scalarWidth
    (setup.execute Reference initial) entry present
  constructor
  · rw [values.2]
    change 0 % 2 ^ scalarWidth < order
    rw [Nat.zero_mod]
    exact positiveOrder
  · intro accepted
    rw [values.1] at accepted
    cases accepted

private theorem four_stage_support {model : ExecutionModel}
    {origin first second final result : RuntimeCtx model.kind}
    (setup : Circuit model origin first) (allocation : Circuit model first second)
    (body : Circuit model second final) (packing : Circuit model final result)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference (model.HiddenState × H))
    (predicate : Store result → Prop) :
    storeSupported ((setup.seq ((allocation.seq body).seq packing)).execute Reference initial)
        predicate ↔
      storeSupported (packing.execute Reference
        (((setup.seq allocation).seq body).execute Reference initial)) predicate := by
  simp only [Circuit.execute_seq, storeSupported_mapHistory]
  rw [Circuit.execute_mapHistory body Reference
    (allocation.execute Reference (setup.execute Reference initial))
    (fun history => (history.1.1, (history.1.2, history.2)))]
  simp only [State.mapHistory_comp, Function.comp_def]
  let state : State final Reference
      (model.HiddenState × (((H × setup.Path) × allocation.Path) × body.Path)) :=
    body.execute Reference (allocation.execute Reference (setup.execute Reference initial))
  let leftUpdate : (((H × setup.Path) × allocation.Path) × body.Path) →
      (H × setup.Path) × (allocation.Path × body.Path) :=
    fun history => (history.1.1, (history.1.2, history.2))
  let rightUpdate : (((H × setup.Path) × allocation.Path) × body.Path) →
      H × ((setup.Path × allocation.Path) × body.Path) :=
    fun history => (history.1.1.1, ((history.1.1.2, history.1.2), history.2))
  change storeSupported (packing.execute Reference
      (state.mapHistory (fun record => (record.1, leftUpdate record.2)))) predicate ↔
    storeSupported (packing.execute Reference
      (state.mapHistory (fun record => (record.1, rightUpdate record.2)))) predicate
  rw [storeSupported_execute_mapHistory packing state leftUpdate predicate,
    storeSupported_execute_mapHistory packing state rightUpdate predicate]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Every positive actual repeated record returns the original secret whenever it returns a word. -/
theorem exponentRepeatedRun_supported_secret
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) (count : Nat) (input : SecretInput problem)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (record : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).Record)
    (positive : 0 < (((exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).execute Reference
        (repeatedOracleInput E problem original).state).block
          record).mass)
    (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (output : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).result record = .optionSome value) :
    value = CShape.wordOfNat (orderWidth problem) input.secret.val := by
  let width := Canonical.Layout.fieldWidth E
  let scalarWidth := orderWidth problem
  let terminal := PublicInput.terminal E scalarWidth
  let measured := inputLeft (PublicInput.terminal_disjoint E scalarWidth)
    (QubitReadouts.input (exponentMeasurementCells p scalarWidth))
  let sample := rawRecoveryInput problem measured
  let base := PublicInput.terminalBaseRef E scalarWidth
  let target := PublicInput.terminalTargetRef E scalarWidth
  let curve := Canonical.Layout.curveSpec E
  let modulus := recoveryModulusSpec problem nontrivial
  let sourceSample := samplingRound E fieldTail sameWidth fits odd problem points seed
  let sourceLocal := samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed
  let sampleCode := BitWord.selectForCircuit sourceSample
  let localSample := BitWord.selectForCircuit_isLocal sourceSample sourceLocal
  let setup := BitWord.selectForCircuit (exponentRepeatedInitial E problem)
  let allocation : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      terminal (persistentCtx terminal width scalarWidth) :=
    retainPersistent (model := .quantum AlgorithmGate.model .empty BitWord.model)
      terminal width scalarWidth
  let body := sampledAttempts sampleCode localSample count curve modulus sample base target
  let packing : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx terminal width scalarWidth) (batchResultCtx terminal width scalarWidth) :=
    packBatchResult (model := .quantum AlgorithmGate.model .empty BitWord.model)
      terminal width scalarWidth
  let initial := PublicInput.persistentInitialState E scalarWidth problem original
  let invariant := fun store : Store (persistentCtx terminal width scalarWidth) =>
    (store.read (.storage (persistentSelected terminal width scalarWidth).toCStorageRef)).toNat <
        problem.order ∧
      ((store.read
          (.storage (persistentAccepted terminal width scalarWidth).toCStorageRef)).toBool =
          true →
        (store.read
          (.storage (persistentSelected terminal width scalarWidth).toCStorageRef)).toNat •
          problem.generator.toMathlib = problem.target.toMathlib)
  have initialized : storeSupported ((setup.seq allocation).execute Reference initial)
      invariant := by
    exact retainPersistent_initialized_invariant setup width scalarWidth problem.order
      (lt_of_lt_of_le (by decide : 0 < 2) nontrivial)
      (fun store =>
        (store.read
          (.storage (persistentSelected terminal width scalarWidth).toCStorageRef)).toNat •
          problem.generator.toMathlib = problem.target.toMathlib) initial
  have maintained : storeSupported (((setup.seq allocation).seq body).execute Reference initial)
      invariant := by
    exact sampledAttempts_supported_validity_on_prefix sampleCode localSample count curve modulus
      sample base target problem.generator.toMathlib problem.target.toMathlib initial
      (fun priorCode => PublicInput.persistentProgram_supported_represents E scalarWidth problem
        priorCode original) (setup.seq allocation) initialized
  have packed : storeSupported
      (packing.execute Reference (((setup.seq allocation).seq body).execute Reference initial))
      (fun store => ∀ returned, store.read (batchResultRead terminal width scalarWidth) =
        .optionSome returned → returned = CShape.wordOfNat scalarWidth input.secret.val) := by
    intro entry present returned same
    exact packBatchResult_supported_secret problem input
      (((setup.seq allocation).seq body).execute Reference initial)
      (fun earlier positive accepted =>
        ⟨(maintained earlier positive).1, (maintained earlier positive).2 accepted⟩)
      entry present returned same
  have completed := (four_stage_support setup allocation body packing initial _).mpr packed
  rw [repeatedRun_execute_persistentInitialState E problem original] at positive
  exact completed record positive value output

/-- The actual output PMF assigns zero probability to every different returned word. -/
theorem exponentRepeatedRun_wrong_probability_zero
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (nontrivial : 2 ≤ problem.order) (count : Nat) (input : SecretInput problem)
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * orderWidth problem)) Reference)
    (value : (CShape.unsignedWord (orderWidth problem)).Value)
    (different : value ≠ CShape.wordOfNat (orderWidth problem) input.secret.val) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).outputDistribution
        (repeatedOracleInput E problem original)
          (.optionSome value) = 0 := by
  by_contra positive
  let run := exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed nontrivial count
  let supplied := repeatedOracleInput E problem original
  have supported : CShape.Value.optionSome value ∈ (run.outputDistribution supplied).support :=
    (PMF.mem_support_iff _ _).mpr positive
  obtain ⟨record, present, output⟩ := (PMF.mem_support_map_iff run.result
    (run.executionDistribution supplied) (.optionSome value)).mp supported
  have mass := (ExecutionState.mem_support_toPMF_iff (run.execute Reference supplied.state)
    (run.execute_normalized supplied) record).mp present
  exact different (exponentRepeatedRun_supported_secret E fieldTail sameWidth fits odd problem
    points seed nontrivial count input original record mass value output)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
