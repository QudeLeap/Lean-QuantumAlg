/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Feedback
import all QuantumAlg.Core.Execution.Interpret.Laws
import QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Full record of the real H/arithmetic/feedback/H prefix

The operator is computed from the same
native H programs, actual selected modular-arithmetic program and previous
output cells as the executable prefix. There is no supplied matrix equality
or instrument certificate. Arbitrary mixed/reference blocks are retained.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The actual finite path remembers every previous-output branch in this prefix. -/
def preparationPath (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    (store : Store (Context base noQuantum m ell width)) :
    (stagePreparation base noQuantum m ell width inverse outputs N unit position).Path :=
  ((), ((),
    (feedbackPath base noQuantum m ell width inverse outputs position position.val le_rfl store,
      ())))

/-- Multiply the actual joint operators in chronological interpreter order. -/
def preparationAction (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) (Reference : Register)
    (store : Store (Context base noQuantum m ell width)) :
    UnitaryOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  let h := UnitaryOperator.prodTensor
    ((single base noQuantum m ell width Gate.HOp).matrix environment.quantum) (1 :
      UnitaryOperator Reference)
  let selectedArithmetic := UnitaryOperator.prodTensor
    ((arithmetic base noQuantum m ell width N (unit ^ (2 ^ position.rev.val))).matrix
      environment.quantum)
    (1 : UnitaryOperator Reference)
  ((h * feedbackAction (environment := environment) base noQuantum m ell width inverse outputs
    position Reference
      position.val le_rfl store) * selectedArithmetic) * h

/-- Complete actual prefix execution, with arbitrary caller store, reference and prior history. -/
lemma stagePreparation_execute (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    (stagePreparation base noQuantum m ell width inverse outputs N unit position).execute
      environment
        Reference state =
      (state.applyUnitary fun entry =>
        preparationAction (environment := environment) base noQuantum m ell width inverse
          outputs N unit position
          Reference entry.1).mapClassical
        (fun entry => (entry.1, (entry.2.1,
          (entry.2.2,
            preparationPath base noQuantum m ell width inverse outputs N unit position
              entry.1)))) := by
  let hProgram := single base noQuantum m ell width Gate.HOp
  let arithmeticProgram :=
    arithmetic base noQuantum m ell width N (unit ^ (2 ^ position.rev.val))
  let hCode : Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
    Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := .empty) hProgram
  let arithmeticCode : Circuit model (Context base noQuantum m ell width)
      (Context base noQuantum m ell width) :=
    Circuit.unitary (allowAllocation := true) (operations := BitWord.model)
      (classicalOracles := .empty) arithmeticProgram
  let feedbackCode := feedbackPrefix base noQuantum m ell width inverse outputs
    position position.val le_rfl
  let hAction : UnitaryOperator ((Context base noQuantum m ell width).register.prod Reference) :=
    UnitaryOperator.prodTensor (hProgram.matrix environment.quantum) (1 : UnitaryOperator Reference)
  let arithmeticAction :
      UnitaryOperator ((Context base noQuantum m ell width).register.prod Reference) :=
    UnitaryOperator.prodTensor (arithmeticProgram.matrix environment.quantum) (1 :
      UnitaryOperator Reference)
  let chosenFeedback := feedbackAction (environment := environment) base noQuantum m ell width
    inverse outputs
    position Reference position.val le_rfl
  let chosenPath := feedbackPath base noQuantum m ell width inverse outputs
    position position.val le_rfl
  let hPath : Store (Context base noQuantum m ell width) → hCode.Path := fun _ => ()
  let arithmeticPath : Store (Context base noQuantum m ell width) → arithmeticCode.Path :=
    fun _ => ()
  let tailPath : Store (Context base noQuantum m ell width) → (feedbackCode.seq hCode).Path :=
    fun stored => (chosenPath stored, hPath stored)
  let middlePath : Store (Context base noQuantum m ell width) →
      (arithmeticCode.seq (feedbackCode.seq hCode)).Path :=
    fun stored => (arithmeticPath stored, tailPath stored)
  have hEquation {H : Type} [Fintype H]
      (earlier : State (Context base noQuantum m ell width) Reference (model.HiddenState × H)) :
      hCode.execute environment Reference earlier =
        (earlier.applyUnitary fun _ => hAction).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, hPath entry.1)))) := by
    have actual := Circuit.execute_unitary (quantumEnvironment := environment) (allowAllocation :=
      true) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := BitWord.model) (services := .empty)
      (ctx := Context base noQuantum m ell width) (Reference := Reference) earlier hProgram
    exact actual.trans (ExecutionState.executionState_mapClassical_congr_decision
      (earlier.applyUnitary fun _ => hAction) _ _ (fun _ => rfl) _ _)
  have arithmeticEquation {H : Type} [Fintype H]
      (earlier : State (Context base noQuantum m ell width) Reference (model.HiddenState × H)) :
      arithmeticCode.execute environment Reference earlier =
        (earlier.applyUnitary fun _ => arithmeticAction).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, arithmeticPath entry.1)))) := by
    have actual := Circuit.execute_unitary (quantumEnvironment := environment) (allowAllocation :=
      true) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := BitWord.model) (services := .empty)
      (ctx := Context base noQuantum m ell width) (Reference := Reference)
      earlier arithmeticProgram
    exact actual.trans (ExecutionState.executionState_mapClassical_congr_decision
      (earlier.applyUnitary fun _ => arithmeticAction) _ _ (fun _ => rfl) _ _)
  have tailEquation {H : Type} [Fintype H]
      (earlier : State (Context base noQuantum m ell width) Reference (model.HiddenState × H)) :
      (feedbackCode.seq hCode).execute environment Reference earlier =
        (earlier.applyUnitary fun entry => hAction * chosenFeedback entry.1).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, tailPath entry.1)))) := by
    have actual := sequence_execute (environment := environment) (ctx := Context base noQuantum m
      ell width)
      feedbackCode hCode Reference chosenFeedback (fun _ => hAction) chosenPath hPath
      (fun earlier => feedbackPrefix_execute base noQuantum m ell width inverse outputs
        position position.val le_rfl earlier)
      (fun earlier => hEquation earlier) earlier
    exact actual.trans (ExecutionState.executionState_mapClassical_congr_decision
      (earlier.applyUnitary fun entry => hAction * chosenFeedback entry.1)
      _ _ (fun _ => rfl) _ _)
  have middleEquation {H : Type} [Fintype H]
      (earlier : State (Context base noQuantum m ell width) Reference (model.HiddenState × H)) :
      (arithmeticCode.seq (feedbackCode.seq hCode)).execute environment Reference earlier =
        (earlier.applyUnitary fun entry =>
          (hAction * chosenFeedback entry.1) * arithmeticAction).mapClassical
          (fun entry => (entry.1, (entry.2.1, (entry.2.2, middlePath entry.1)))) := by
    have actual := sequence_execute (environment := environment) (ctx := Context base noQuantum m
      ell width)
      arithmeticCode (feedbackCode.seq hCode) Reference (fun _ => arithmeticAction)
      (fun stored => hAction * chosenFeedback stored) arithmeticPath tailPath
      (fun earlier => arithmeticEquation earlier) (fun earlier => tailEquation earlier) earlier
    exact actual.trans (ExecutionState.executionState_mapClassical_congr_decision
      (earlier.applyUnitary fun entry => (hAction * chosenFeedback entry.1) * arithmeticAction)
      _ _ (fun _ => rfl) _ _)
  change (hCode.seq (arithmeticCode.seq (feedbackCode.seq hCode))).execute environment
    Reference state = _
  have actual := sequence_execute (environment := environment) (ctx := Context base noQuantum m ell
    width)
    hCode (arithmeticCode.seq (feedbackCode.seq hCode)) Reference (fun _ => hAction)
    (fun stored => (hAction * chosenFeedback stored) * arithmeticAction)
    hPath middlePath
    (fun earlier => hEquation earlier) (fun earlier => middleEquation earlier) state
  exact actual.trans (ExecutionState.executionState_mapClassical_congr_decision
    (state.applyUnitary fun entry =>
      preparationAction (environment := environment) base noQuantum m ell width inverse outputs
        N unit position
        Reference entry.1) _ _ (fun _ => rfl) _ _)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
