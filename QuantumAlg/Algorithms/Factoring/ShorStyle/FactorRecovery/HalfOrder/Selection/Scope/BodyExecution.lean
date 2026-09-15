/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Records

/-!
# Complete execution of the actual initialized half-factor body

The two real constant-loading circuits compose with the actual left-priority
factor circuit. The resulting equality retains the full store, genuine path
and arbitrary external reference blocks of that same execution.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem one_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (ConstantWord.circuit (oneRef ctx N) 1).execute Reference state =
      state.mapClassical (fun entry => ((oneStep entry.1).1, (entry.2, (oneStep entry.1).2))) := by
  refine (ConstantWord.constantWord_fold_execute (oneRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) 1)) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store (context ctx N) ×
        (History × (ConstantWord.circuit (oneRef ctx N) 1).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((oneStep entry.1).1, (entry.2, (oneStep entry.1).2))))
    (Subsingleton.elim _ _)

private theorem modulus_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (ConstantWord.circuit (modulusRef ctx N) N).execute Reference state =
      state.mapClassical (fun entry =>
        ((modulusStep entry.1).1, (entry.2, (modulusStep entry.1).2))) := by
  refine (ConstantWord.constantWord_fold_execute (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store (context ctx N) ×
        (History × (ConstantWord.circuit (modulusRef ctx N) N).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((modulusStep entry.1).1,
          (entry.2, (modulusStep entry.1).2)))) (Subsingleton.elim _ _)

private theorem modulusTail_execute
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (Circuit.seq (ConstantWord.circuit (modulusRef ctx N) N)
        (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output))).execute
        Reference state =
      state.mapClassical (fun entry => ((modulusTailStep halfPower output entry.1).1,
        (entry.2, (modulusTailStep halfPower output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (ConstantWord.circuit (modulusRef ctx N) N)
    (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output)) modulusStep
    (NativeHalfFactor.step (liftInput halfPower) (cells ctx N) (liftWrite output))
    modulus_execute
    (NativeHalfFactor.code_execute (liftInput halfPower) (cells ctx N) (liftWrite output))
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store (context ctx N) × (History ×
        (Circuit.seq (ConstantWord.circuit (modulusRef ctx N) N)
          (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output))).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((modulusTailStep halfPower output entry.1).1,
          (entry.2, (modulusTailStep halfPower output entry.1).2)))) (Subsingleton.elim _ _)

/-- The actual initialized body executes its exact physical store and complete path on CQ blocks. -/
theorem body_execute (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((bodyStep halfPower output entry.1).1,
        (entry.2, (bodyStep halfPower output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (ConstantWord.circuit (oneRef ctx N) 1)
    (.seq (ConstantWord.circuit (modulusRef ctx N) N)
      (NativeHalfFactor.code (liftInput halfPower) (cells ctx N) (liftWrite output))) oneStep
    (modulusTailStep halfPower output) one_execute (modulusTail_execute halfPower output)
    Reference state).trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store (context ctx N) × (History × (body halfPower output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((bodyStep halfPower output entry.1).1,
          (entry.2, (bodyStep halfPower output entry.1).2)))) (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
