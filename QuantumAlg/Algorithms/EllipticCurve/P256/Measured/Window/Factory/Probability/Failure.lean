/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.PublicInput.Storage
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Execution
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Mass
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Conditional
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect

/-! # Three actual paid P-256 rounds fail with probability at most one in 125

The unchanged original point domain is the only input premise. The actual factory
supplies preparation and per-round candidate mass internally. Every supplied
Reference and the complete classical history remain in the calculation. -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalRoutines.EllipticCurve

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma suppliedState_mass (I : DomainParameters.PublicKeyInstance)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference) :
    (suppliedState I supplied).mass = 1 :=
  (supplied.state.mapClassical_mass _).trans supplied.normalized

private lemma public_retainedInputs_internal_candidateMass (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment) :
    (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).InternalCandidateMass environment
        (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib
        I.publicKey.toMathlib ((4 : ℝ) / 5) := by
  exact factory_internalCandidateMass I
    (tableContext_wires (publicFrame I) (publicFrame_noQuantum I))
    (resultsAfterTables (publicFrame I) (publicFrame_noQuantum I))
    (tableFrame (publicFrame I) (publicFrame_noQuantum I))
    (originalInputAfterTables (publicFrame I) (publicFrame_noQuantum I) (publicBaseRef I))
    (originalInputAfterTables (publicFrame I) (publicFrame_noQuantum I) (publicTargetRef I))
    (FiniteCyclicDLP.Canonical.Probability.SecretInput.ofKnownOrderProblem
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))) environment

private def FinalizedNoneBoundStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    let original := retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    original.InternalPreparation environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib →
    original.InternalCandidateMass environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
        ((4 : ℝ) / 5) →
    let prefixCode := paidPrefix (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    let entered := prefixCode.execute environment Reference (suppliedState I supplied)
    ((original.runFinalized (services := .empty)).code.execute
      environment Reference entered).effectWeight
      (fun entry => if entry.1.read
        (CandidateCheck.Native.batchResultRead
          (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260) = .optionNone then
        Effect.one
          ((CandidateCheck.Native.batchResultCtx
            (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260).register.prod
              Reference)
      else Effect.zero
          ((CandidateCheck.Native.batchResultCtx
            (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260).register.prod
              Reference)) ≤ ((1 : ℝ) / 125)

private lemma finalizedNoneBound_proof : FinalizedNoneBoundStatement := by
  intro I environment Reference supplied valid original prepared quality prefixCode entered
  have supported := public_paidPrefix_inputsSupported I environment supplied valid
  have bound := original.runFinalized_failure_le_of_internal_evidence environment
    (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
    ((4 : ℝ) / 5) (by norm_num) prepared quality entered supported
  have mass : entered.mass = 1 :=
    (prefixCode.execute_mass environment Reference (suppliedState I supplied)).trans
      (suppliedState_mass I supplied)
  exact bound.trans_eq (by rw [mass]; norm_num)

private def ConditionalPaidNoneStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    let original := retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    original.InternalPreparation environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib →
    original.InternalCandidateMass environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib
        ((4 : ℝ) / 5) →
    (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).outputDistribution environment supplied
        .optionNone ≤ ENNReal.ofReal ((1 : ℝ) / 125)

private lemma conditionalPaidNone_proof : ConditionalPaidNoneStatement := by
  intro I environment Reference supplied valid original prepared quality
  let prefixCode := paidPrefix (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
    (publicBaseRef I) (publicTargetRef I)
  have finalBound := finalizedNoneBound_proof I environment (Reference := Reference)
    supplied valid prepared quality
  rw [AlgorithmRun.outputDistribution_apply_eq_effectWeight]
  apply ENNReal.ofReal_le_ofReal
  rw [paidRun_execute_recorded I environment supplied]
  change ((prefixCode.seq (original.runFinalized (services := .empty)).code).execute
    environment Reference (suppliedState I supplied)).effectWeight
    (fun entry => if entry.1.read
      (CandidateCheck.Native.batchResultRead
        (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260) = .optionNone then
      Effect.one
        ((CandidateCheck.Native.batchResultCtx
          (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260).register.prod
            Reference)
    else Effect.zero
        ((CandidateCheck.Native.batchResultCtx
          (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260).register.prod
            Reference))
      ≤ ((1 : ℝ) / 125)
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]
  exact finalBound

private def PaidNoneBridgeStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).outputDistribution environment supplied
        .optionNone ≤ ENNReal.ofReal ((1 : ℝ) / 125)

private lemma paidNoneBridge_proof : PaidNoneBridgeStatement := by
  intro I environment Reference supplied valid
  exact conditionalPaidNone_proof I environment supplied valid
    (public_retainedInputs_internal_preparation I environment)
    (public_retainedInputs_internal_candidateMass I environment)

/-- Three literal paid rounds fail at most one time in 125 on the original input domain. -/
lemma paidRun_none_le (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState) :
    (paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).outputDistribution environment supplied
        .optionNone ≤ ENNReal.ofReal ((1 : ℝ) / 125) :=
  paidNoneBridge_proof I environment supplied valid

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
