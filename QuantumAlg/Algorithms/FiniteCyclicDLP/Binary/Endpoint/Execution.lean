/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Cycle
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Ambient
public import QuantumAlg.Util.Real.LogCeiling
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Cycle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Run
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Encoding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Scalar
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun

import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Finite-cyclic discrete logarithms with one actual binary quantum bank

The complete execution uses the minimal binary group representation, retains
its classical samples and physically resets the reused bank after every sample.
All displayed native resources and complete-run quantum-time bounds belong
to this same execution, including every positive order and arbitrary external
references [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma output_atom_eq_relational {model : ExecutionModel}
    {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (selected : AlgorithmRun model pre post shape)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    selected.outputDistribution environment input value =
      (selected.relationalDistribution environment input).toOuterMeasure
        {pair | pair.2 = value} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- The sole candidate is the complete endpoint run. -/
@[expose] public def algorithm (P : KnownOrderProblem G) :
    Algorithm (Reusable.model P) Reusable.pre (outputContext P)
      (.option (.unsignedWord (OrderPreparation.width P))) where
  run := run P

private lemma accepted_probability (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    ((algorithm P).relationalDistribution environment input).toOuterMeasure
        {pair | accepts secret pair.1 pair.2} =
      (run P).outputDistribution environment input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  change ((run P).relationalDistribution environment input).toOuterMeasure
      {pair | pair.2 = .optionSome
        (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)} = _
  exact (output_atom_eq_relational (run P) input _).symm

private lemma solves_success (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        successLowerBound.value ≤
          ((algorithm P).relationalDistribution environment input).toOuterMeasure
            {pair | accepts secret pair.1 pair.2} := by
  intro valid _initialized
  subst environment
  change ENNReal.ofReal ((2 : Real) / 3) ≤ _
  rw [accepted_probability]
  exact binaryEndpoint_run_success P secret input

private lemma solves_states (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (_secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        ∀ requirement ∈ ([] : List (StateRequirement Reusable.pre (outputContext P))),
          requirement.Holds input.caller
            ((algorithm P).run.finalState environment Reference input.state) := by
  intro _valid _initialized _requirement present
  exact False.elim (List.not_mem_nil present)

private lemma solves_borrowed (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (_secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        (algorithm P).run.RestoresBorrowed environment input := by
  intro _valid _initialized
  have restored := Circuit.borrowedRestored_of_noBorrowedQuantum (code P) environment
    RuntimeCtx.borrowedQuantumWires_empty Reference
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
  have history := Execution.observeBorrowed_mapClassical input.state
    (fun value => (value.1, (value.2, value.1))) (fun _ => rfl)
  change (code P).BorrowedRestored Reference input.state
    ((code P).execute environment Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1)))))
  unfold Circuit.BorrowedRestored at restored ⊢
  rw [restored]
  refine Eq.trans ?_ history
  apply congrArg (Execution.observeBorrowed Reference)
  exact ExecutionState.executionState_mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _

private lemma solves_events (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (_secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).run.code.resourcePool path ≤ eventBudget P := by
  intro _valid _initialized path _supported
  exact binaryEndpoint_code_pool_le P path

private lemma solves_resident (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (_secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).run.code.peakResidentSpace path ≤
            residentBudget P := by
  intro _valid _initialized path _supported
  exact binaryEndpoint_code_resident_le P path

private lemma solves_auxiliary (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (_secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).run.code.peakAuxiliarySpace path ≤
            auxiliaryBudget P := by
  intro _valid _initialized path _supported
  exact binaryEndpoint_code_auxiliary_le P path

private lemma solves_time (P : KnownOrderProblem G)
    (environment : (Reusable.model P).Environment)
    (_secret : FiniteCyclicDLP.Input P) {Reference : Register}
    (input : Execution.OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference) :
    environment = Reusable.sourceEnvironment P →
      True →
        ∀ path, (algorithm P).run.Supports environment Reference input.state path →
          (algorithm P).quantumTime path ≤ quantumTimeLimit P := by
  intro _valid _initialized path _supported
  exact (Circuit.quantumTime_le_unitDepth _ _).trans (binaryEndpoint_code_depth_le P path)

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
