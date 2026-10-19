/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Failure
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Candidate
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Support
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Initialization
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# The actual packed declared-query ECDLP value is the original canonical secret

Allocation initializes the real first-success latches. Every actual prefix
retains both original public points, and the complete native checker preserves
the selected value's range and natural-scalar point equation. The one final
option pack therefore returns only the original canonical secret, including
zero further rounds, arbitrary references and correlated execution histories.
No candidate, success distribution or secret is an execution input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local instance] Classical.decEq Classical.propDecidable
attribute [local irreducible] sampleUnderPersistent retainPersistent

private lemma allocation_selected_initialized {model : ExecutionModel}
    {environment : model.Environment}
    {origin ctx : RuntimeCtx model.kind} (setup : Circuit model origin ctx)
    {width scalar : Nat} (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalar)
    (basePoint targetPoint : ClassicalAlgorithms.EllipticCurve.Point curve)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State origin Reference (model.HiddenState × History)) :
    storeSupported ((setup.seq (retainPersistent ctx width scalar)).execute environment Reference
      initial)
      (fun store => selectedInvariant curve modulus basePoint targetPoint (selectedPair store)) :=
  by
  refine (storeSupported_seq setup (retainPersistent ctx width scalar) initial
    (fun store => selectedInvariant curve modulus basePoint targetPoint
      (selectedPair store))).mpr ?_
  intro entry present
  have latches := retainPersistent_latches_supported width scalar
    (setup.execute environment Reference initial) entry present
  constructor
  · change (entry.1.read (.storage (persistentSelected ctx width scalar).toCStorageRef)).toNat < _
    rw [latches.2]
    simp only [CShape.initialValue_unsignedWord, CShape.wordOfNat_val, Nat.zero_mod]
    exact lt_of_lt_of_le (by decide : 0 < 2) modulus.two_le
  · intro accepted
    exact False.elim (Bool.false_ne_true (latches.1.symm.trans accepted))

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

private lemma code_supported_correct (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (secretInput : FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I))
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Sampling.pre I) Reference
      ((Sampling.executionModel I).HiddenState × History))
    (admitted : ∀ entry, 0 < (initial.block entry).mass → entry.1 = Runtime.Context.inputStore I) :
    storeSupported ((code I expansion nontrivial count).execute (Sampling.sourceEnvironment I A)
      Reference initial)
      (fun store => ∀ value, store.read
        (batchResultRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)) =
          .optionSome value → value.toNat = secretInput.secret.val) := by
  let ctx := Sampling.Reuse.context I
  let width := fieldWidth E
  let scalar := scalarWidth I
  let setup := Sampling.Reuse.initialCode I
  let allocation : Circuit (Sampling.executionModel I) ctx (persistentCtx ctx width scalar) :=
    retainPersistent (model := Sampling.executionModel I) ctx width scalar
  let body := sampledAttempts (Sampling.Reuse.code (allowAllocation := false) I expansion)
    count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
  let packing : Circuit (Sampling.executionModel I)
      (persistentCtx ctx width scalar) (batchResultCtx ctx width scalar) :=
    packBatchResult (model := Sampling.executionModel I) ctx width scalar
  let invariant := fun store : Store (persistentCtx ctx width scalar) =>
    (store.read (.storage (persistentSelected ctx width scalar).toCStorageRef)).toNat <
        (modulus I nontrivial).modulus ∧
      ((store.read (.storage (persistentAccepted ctx width scalar).toCStorageRef)).toBool = true →
        (store.read (.storage (persistentSelected ctx width scalar).toCStorageRef)).toNat •
          I.basePoint.toMathlib = I.targetPoint.toMathlib)
  have allocated : storeSupported ((setup.seq allocation).execute (Sampling.sourceEnvironment I A)
    Reference initial) invariant := by
    exact allocation_selected_initialized setup (curve E) (modulus I nontrivial)
      I.basePoint.toMathlib I.targetPoint.toMathlib initial
  have checked : storeSupported (((setup.seq allocation).seq body).execute
    (Sampling.sourceEnvironment I A) Reference initial)
      invariant := by
    exact sampledAttempts_supported_validity_on_prefix
      (Sampling.Reuse.code (allowAllocation := false) I expansion)
      count (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
      I.basePoint.toMathlib I.targetPoint.toMathlib initial
      (fun priorCode => ecdlpRecovery_prefix_represents I A initial admitted priorCode)
      (setup.seq allocation) allocated
  have regrouped : storeSupported ((setup.seq (allocation.seq body)).execute
    (Sampling.sourceEnvironment I A) Reference initial)
      invariant := (storeSupported_seq_assoc setup allocation body initial invariant).mpr checked
  let property := fun store : Store (batchResultCtx ctx width scalar) =>
    ∀ value, store.read (batchResultRead ctx width scalar) = .optionSome value →
      value.toNat = secretInput.secret.val
  change storeSupported ((setup.seq ((allocation.seq body).seq packing)).execute
    (Sampling.sourceEnvironment I A) Reference initial) property
  refine (storeSupported_seq_assoc setup (allocation.seq body) packing initial property).mpr ?_
  refine (storeSupported_seq (setup.seq (allocation.seq body)) packing initial property).mpr ?_
  intro entry present value output
  exact packBatchResult_supported_property (fun selected => selected.toNat = secretInput.secret.val)
    ((setup.seq (allocation.seq body)).execute (Sampling.sourceEnvironment I A) Reference initial)
    (fun original positive accepted =>
      (bounded_scalar_target_iff I secretInput _ (regrouped original positive).1).mp
        ((regrouped original positive).2 accepted)) entry present value output

/-- Every positive complete record carries only the original canonical secret in its real option. -/
public lemma ecdlpRecovery_run_supported_correct (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (secretInput : FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I))
    {Reference : Register}
    (original : OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState)
    (record : (run I expansion nontrivial count).Record)
    (positive : 0 < (((run I expansion nontrivial count).execute (Sampling.sourceEnvironment I A)
      Reference original.state).block
      record).mass) (value : (CShape.unsignedWord (scalarWidth I)).Value)
    (output : (run I expansion nontrivial count).result record = .optionSome value) :
    value.toNat = secretInput.secret.val := by
  let initial := original.state.mapClassical (fun value => (value.1, (value.2, value.1)))
  have admitted : ∀ entry, 0 < (initial.block entry).mass →
      entry.1 = Runtime.Context.inputStore I := by
    intro entry present
    obtain ⟨source, same, positive⟩ :=
      (ExecutionState.mapClassical_block_mass_pos_iff original.state
        (fun value => (value.1, (value.2, value.1))) entry).mp present
    have expected := valid source.1 (original.caller_local_mass_pos_of_joint source positive)
    exact (congrArg Prod.fst same).symm.trans expected
  exact code_supported_correct I A expansion nontrivial count secretInput initial admitted
    record positive value output

/-- A supported actual optional output is the canonical secret, for every finite run count. -/
public lemma ecdlpRecovery_run_output_correct (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (secretInput : FiniteCyclicDLP.Canonical.Probability.SecretInput (problem I))
    {Reference : Register}
    (original : OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference)
    (valid : inputDomain I original.caller.localState)
    (value : (CShape.unsignedWord (scalarWidth I)).Value)
    (supported : .optionSome value ∈
      ((run I expansion nontrivial count).outputDistribution (Sampling.sourceEnvironment I A)
        original).support) :
    value.toNat = secretInput.secret.val := by
  obtain ⟨record, present, output⟩ := (PMF.mem_support_map_iff
    (run I expansion nontrivial count).result
    ((run I expansion nontrivial count).executionDistribution (Sampling.sourceEnvironment I A)
      original) (.optionSome value)).mp
      supported
  have positive := (ExecutionState.mem_support_toPMF_iff
    ((run I expansion nontrivial count).execute (Sampling.sourceEnvironment I A) Reference
      original.state)
    ((run I expansion nontrivial count).execute_normalized (Sampling.sourceEnvironment I A)
      original) record).mp present
  exact ecdlpRecovery_run_supported_correct I A expansion nontrivial count secretInput
    original valid record positive value output

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
