/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.PublicInput.Storage
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Execution
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Recovery.Contract
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized.Soundness

/-! # Sound actual paid results on the unchanged public input domain -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalRoutines.EllipticCurve
open FiniteCyclicDLP.Canonical.Probability (SecretInput)

attribute [local irreducible] Circuit.execute Circuit.pathFintype

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private def GroupEquation (I : DomainParameters.PublicKeyInstance) (scalar : Nat) : Prop :=
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  scalar • (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib = I.publicKey.toMathlib

private def ResultValid (I : DomainParameters.PublicKeyInstance) (bound : Nat)
    (store : Store (CandidateCheck.Native.batchResultCtx
      (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260)) : Prop :=
  ∀ value, store.read (CandidateCheck.Native.batchResultRead
    (tableContext (publicFrame I) (publicFrame_noQuantum I)) 256 260) = .optionSome value →
    value.toNat < bound ∧ GroupEquation I value.toNat

private def FinalizedValidStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    let original := retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    let prefixCode := paidPrefix (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    ∀ record, 0 < (((original.runFinalized (services := .empty)).code.execute
      environment Reference (prefixCode.execute environment Reference
        (suppliedState I supplied))).block record).mass →
      ResultValid I original.order.modulus record.1

private lemma finalizedValid_proof : FinalizedValidStatement := by
  intro I environment Reference supplied valid original prefixCode
  let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  have prepared : original.InternalPreparation environment
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib :=
    public_retainedInputs_internal_preparation (services := .empty) I environment
  exact original.runFinalized_some_valid (services := .empty) environment
    (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib I.publicKey.toMathlib prepared
    (prefixCode.execute environment Reference (suppliedState I supplied))
    (public_paidPrefix_inputsSupported I environment supplied valid)

private def PaidCodeValidStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    let original := retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    let prefixCode := paidPrefix (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    ∀ record, 0 < (((prefixCode.seq (original.runFinalized (services := .empty)).code).execute
      environment Reference (suppliedState I supplied)).block record).mass →
      ResultValid I original.order.modulus record.1

private lemma paidCodeValid_proof : PaidCodeValidStatement := by
  intro I environment Reference supplied valid
  exact Circuit.supported_store_seq environment
    (paidPrefix (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I))
    ((retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).runFinalized (services := .empty)).code
    Reference (suppliedState I supplied)
    (ResultValid I (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)).order.modulus)
    (finalizedValid_proof I environment supplied valid)

private def PaidRunStoreStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    let run := paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    ∀ record, 0 < ((run.execute environment Reference supplied.state).block record).mass →
      ResultValid I (retainedInputs (publicFrame I) (publicFrame_noQuantum I) I
        (publicBaseRef I) (publicTargetRef I)).order.modulus record.1

private lemma paidRunStore_proof : PaidRunStoreStatement := by
  intro I environment Reference supplied valid
  refine fun record positive => ?_
  have positiveCode := (congrArg
    (fun state : ExecutionState _ _ => 0 < (state.block record).mass)
    (paidRun_execute_recorded I environment supplied)).mp positive
  exact paidCodeValid_proof I environment supplied valid record positiveCode

private def PaidRunValidStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference),
    ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState →
    let run := paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    ∀ record, 0 < ((run.execute environment Reference supplied.state).block record).mass →
      ∀ value, run.result record = .optionSome value →
        value.toNat < (Cascade.ecdlpInstance I).subgroupOrder ∧
          GroupEquation I value.toNat

private lemma paidRunValid_proof : PaidRunValidStatement := by
  intro I environment Reference supplied valid run record positive value output
  have facts := paidRunStore_proof I environment supplied valid record positive value output
  constructor
  · exact facts.1.trans_eq (inputs_order I
      (tableContext_wires (publicFrame I) (publicFrame_noQuantum I))
      (resultsAfterTables (publicFrame I) (publicFrame_noQuantum I))
      (tableFrame (publicFrame I) (publicFrame_noQuantum I))
      (originalInputAfterTables (publicFrame I) (publicFrame_noQuantum I) (publicBaseRef I))
      (originalInputAfterTables (publicFrame I) (publicFrame_noQuantum I) (publicTargetRef I)))
  · exact facts.2

/-- Every present actual result is bounded and satisfies the original public point equation. -/
lemma paidRun_supported_valid (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState) :
    let run := paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    ∀ record, 0 < ((run.execute environment Reference supplied.state).block record).mass →
      ∀ value, run.result record = .optionSome value →
        value.toNat < (Cascade.ecdlpInstance I).subgroupOrder ∧
          (let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩;
            value.toNat • (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib =
              I.publicKey.toMathlib) :=
  paidRunValid_proof I environment supplied valid

private lemma word_eq_wordOfNat_toNat {width : Nat} (value : CShape.Word width) :
    value = CShape.wordOfNat width value.toNat := by
  cases value with
  | unsignedWord value =>
      apply congrArg CShape.Value.unsignedWord
      apply Fin.ext
      exact (Nat.mod_eq_of_lt value.isLt).symm

/-- A present actual paid result is the unique secret word; the run is secret-independent. -/
lemma paidRun_supported_secret (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    {Reference : Register} (supplied : OracleInput .empty (publicFrame I) Reference)
    (valid : ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
      (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) supplied.caller.localState) :
    let run := paidRun (services := .empty) (publicFrame I) (publicFrame_noQuantum I) I
      (publicBaseRef I) (publicTargetRef I)
    ∀ record, 0 < ((run.execute environment Reference supplied.state).block record).mass →
      ∀ value, run.result record = .optionSome value →
        value = CShape.wordOfNat 260 input.secret.val := by
  intro run record positive value output
  have facts := paidRun_supported_valid I environment supplied valid record positive value output
  exact (word_eq_wordOfNat_toNat value).trans
    (Recovery.bounded_word_eq_secret I input value.toNat facts.1 facts.2)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
