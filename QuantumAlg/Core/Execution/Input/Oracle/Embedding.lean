/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Embedding
public import QuantumAlg.Core.Execution.Input.Oracle.Reference
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Actual joint inputs at a physical child placement

The child receives the existing caller and service state through the same
physical split used by execution. The complement remains a quantum reference;
its classical cells are summed without conditioning. A second observation
retains just the original external reference. Both have the same local joint
input and therefore the same arbitrary admission predicates
[dW19, qcnotes.tex:5381,5394,6827]. No service is sampled or initialized here.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)
  {oracles : ClassicalOracleModel} {Reference : Register}

/-- Physical splitting and forgetting complement store labels retain total input mass. -/
public lemma contextEmbedding_framedInput_normalized
    (input : OracleInput oracles caller Reference) :
    ((placement.split input.state).mapClassical
      (fun entry => (entry.1, entry.2.2))).IsNormalized :=
  (ExecutionState.mapClassical_mass _ _).trans
    ((placement.contextEmbedding_split_mass input.state).trans input.normalized)

/-- Project the actual input and retain all complement quantum systems in the reference. -/
@[expose] public def framedInput (input : OracleInput oracles caller Reference) :
    OracleInput oracles localCtx (placement.frame.register.prod Reference) where
  state := (placement.split input.state).mapClassical fun entry => (entry.1, entry.2.2)
  normalized := contextEmbedding_framedInput_normalized placement input

/-- Observe the same child input against the caller's original external reference. -/
@[expose] public def localInput (input : OracleInput oracles caller Reference) :
    OracleInput oracles localCtx Reference :=
  (placement.framedInput input).forgetReferenceFrame

/-- Removing the complement reference cannot change the service initialization predicate. -/
public lemma contextEmbedding_localInput_localState
    (input : OracleInput oracles caller Reference) :
    (placement.localInput input).localState = (placement.framedInput input).localState :=
  OracleInput.oracleInput_forgetReferenceFrame_localState _

/-- Removing the complement reference cannot change the local caller validity predicate. -/
public lemma contextEmbedding_localInput_caller_localState
    (input : OracleInput oracles caller Reference) :
    (placement.localInput input).caller.localState =
      (placement.framedInput input).caller.localState :=
  OracleInput.oracleInput_forgetReferenceFrame_caller_localState _

end

end QuantumAlg.ContextEmbedding
