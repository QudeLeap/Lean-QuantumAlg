/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.PublicInput
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.SuccessFloor.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Loop
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure.Boundary

/-!
# Actual original ECDLP recovery failure through every real prefix

Each actual unaccepted state has the original selected-candidate floor after
its own paid reset and sample. The original borrowed point values hold on
every supported prefix. The actual finite loop therefore contracts failure
mass, and the real final optional pack reports exactly that remaining mass.
No independent-copy distribution or caller-supplied intermediate state is
part of this result. Zero rounds and unnormalized reference blocks are included.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open FiniteCyclicDLP.Concrete.Amplification

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] underPersistent retainPersistent

private theorem indicator_decision_weight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (condition : C → Prop)
    (first second : DecidablePred condition) :
    state.effectWeight (fun entry => @ite (Effect R) (condition entry) (first entry)
        (Effect.one R) (Effect.zero R)) =
      state.effectWeight (fun entry => @ite (Effect R) (condition entry) (second entry)
        (Effect.one R) (Effect.zero R)) := by
  cases Subsingleton.elim first second
  rfl

private theorem four_stage_weight {kind : ProblemKind}
    {origin first second final result : RuntimeCtx kind}
    (setup : Circuit origin first) (allocation : Circuit first second)
    (body : Circuit second final) (packing : Circuit final result)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (effects : Store result → Effect (result.register.prod Reference)) :
    ((setup.seq ((allocation.seq body).seq packing)).execute Reference initial).effectWeight
        (fun entry => effects entry.1) =
      (packing.execute Reference (((setup.seq allocation).seq body).execute
        Reference initial)).effectWeight (fun entry => effects entry.1) := by
  simp only [Circuit.execute_seq, Circuit.execute_mapHistory, State.effectWeight_mapHistory]

private theorem initialized_failure_weight {kind : ProblemKind}
    {origin ctx : RuntimeCtx kind} (setup : Circuit origin ctx) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
        ((setup.seq (retainPersistent ctx width scalarWidth)).execute Reference initial) =
      initial.mass := by
  exact (storedWeight_seq setup (retainPersistent ctx width scalarWidth) initial
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))).trans
    ((retainPersistent_failure_weight width scalarWidth (setup.execute Reference initial)).trans
      (setup.execute_mass Reference initial))

private theorem floor_le_one {G : Type} [Group G] (problem : FiniteCyclicDLP.KnownOrderProblem G) :
    attemptFloor problem ≤ 1 := by
  have nonnegative := Factoring.FailureBudget.value_nonneg (sourceFailureBudget problem)
    (sourceFailureBudget_strictlyWellFormed problem).toWellFormed
  rw [sourceFailureBudget_value] at nonnegative
  linarith

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual final optional failure mass has the original finite geometric bound. -/
theorem nativeECDLP_recoveryRun_none_weight_le
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State (Runtime.Context.pre I) Reference H)
    (valid : ∀ entry, 0 < (initial.block entry).mass → entry.1 = Runtime.Context.inputStore I) :
    ((recoveryRun (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I B A
      count (Runtime.Context.baseRef I) (Runtime.Context.targetRef I)).code.execute
        Reference initial).effectWeight (fun entry =>
          if entry.1.read (batchResultRead
            (context (Runtime.Context.pre I) (PublicInput.nativeECDLP_input_quantumWires I) I)
            (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I))) = .optionNone then
            Effect.one ((recoveryContext (Runtime.Context.pre I)
              (PublicInput.nativeECDLP_input_quantumWires I) I).register.prod Reference)
          else Effect.zero ((recoveryContext (Runtime.Context.pre I)
            (PublicInput.nativeECDLP_input_quantumWires I) I).register.prod Reference)) ≤
      (1 - attemptFloor (problem I)) ^ count * initial.mass := by
  let base := Runtime.Context.pre I
  have noQuantum := PublicInput.nativeECDLP_input_quantumWires I
  let width := Layout.fieldWidth E
  let scalarWidth := FiniteCyclicDLP.orderWidth (problem I)
  let terminal := context base noQuantum I
  let sampleRef := sampleInput base noQuantum I
  let baseRef := liftInput base noQuantum I (Runtime.Context.baseRef I)
  let targetRef := liftInput base noQuantum I (Runtime.Context.targetRef I)
  let curve := Layout.curveSpec E
  let modulus := recoveryModulus I
  let sampleCode := reusedSample base noQuantum I B A
  have supported := nativeECDLP_reusedSample_isLocal base noQuantum I B A
  let setup := allocate base noQuantum I
  let allocation := retainPersistent terminal width scalarWidth
  let body := sampledAttempts sampleCode supported count curve modulus sampleRef baseRef targetRef
  let packing := packBatchResult terminal width scalarWidth
  let lower := attemptFloor (problem I)
  have geometric := sampledAttempts_failure_weight_le_on_prefix sampleCode supported count
    curve modulus sampleRef baseRef targetRef I.basePoint.toMathlib I.targetPoint.toMathlib
    initial (fun priorCode => PublicInput.nativeECDLP_persistent_supported_represents I
      priorCode initial valid) lower (floor_le_one (problem I))
    (fun K _ state => by
      have floor := nativeECDLP_persistent_candidate_weight_bound base noQuantum I B A state
      exact floor.trans_eq (indicator_decision_weight _ _ _ _)) (setup.seq allocation)
  rw [initialized_failure_weight] at geometric
  have packed := packBatchResult_none_weight width scalarWidth
    (((setup.seq allocation).seq body).execute Reference initial)
  have completed := (four_stage_weight setup allocation body packing initial
    (fun store => if store.read (batchResultRead terminal width scalarWidth) = .optionNone then
      Effect.one ((batchResultCtx terminal width scalarWidth).register.prod Reference)
    else Effect.zero ((batchResultCtx terminal width scalarWidth).register.prod Reference))).trans
      packed
  exact completed.trans_le geometric

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
