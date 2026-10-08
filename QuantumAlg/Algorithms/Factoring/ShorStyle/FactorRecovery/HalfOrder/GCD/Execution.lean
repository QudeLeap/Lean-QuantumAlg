/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Execution
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.GCD.LexicalSemantics
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete actual records of the two scoped half-power GCD calls

The records follow the real adjacent-word instructions, literal modulus load,
result initialization and expanded Euclidean circuit. Both enclosing operand
scopes are actually entered and released. All execution equalities retain
the entire original quantum-reference density blocks.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The real result initialization precedes the existing Euclidean record. -/
def gcdTailStep (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) : Store (context ctx N) × (gcdTail (model := model)
      output).Path :=
  let cleared := BitWord.instructionStep (execution := model) (clearOp output) store
  let next := NumberTheory.GCD.lexicalStep (model := model) (operands ctx N) (liftWrite output)
    cleared.1
  (next.1, (cleared.2, next.2))

/-- The literal modulus-load record feeds its actual written word to the GCD. -/
def loadTailStep (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) : Store (context ctx N) ×
      (Circuit.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N) (gcdTail (model :=
        model) output)).Path :=
  let loaded := ConstantWord.foldStep (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) store
  let reduced := gcdTailStep (model := model) output loaded.1
  (reduced.1, (loaded.2, reduced.2))

/-- The first real adjacent-word result is the operand read by the following actual GCD. -/
def bodyStep (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) : Store (context ctx N) ×
      (body (model := model) successor halfPower output).Path :=
  let adjacent := NativeAdjacentWord.step (model := model) successor (liftInput halfPower)
    (adjacentRef ctx N) store
  let reduced := loadTailStep (model := model) output adjacent.1
  (reduced.1, (adjacent.2, reduced.2))

/-- Enter and release the actual modulus operand around the same physical body. -/
def innerStep (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (adjacentContext ctx N)) : Store (adjacentContext ctx N) ×
      (body (model := model) successor halfPower output).Path :=
  let next := bodyStep (model := model) successor halfPower output
    (store.pushWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (adjacentContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh next.1,
    next.2)

/-- Both real operand scopes return the actual GCD store and path to the original context. -/
def step (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) (store : Store ctx) :
    Store ctx × (code (model := model) successor halfPower output).Path :=
  let next := innerStep (model := model) successor halfPower output
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh next.1, next.2)

private theorem gcdTail_execute (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (gcdTail (model := model) output).execute Reference state =
      state.mapClassical (fun entry => ((gcdTailStep (model := model) output entry.1).1,
        (entry.2.1, (entry.2.2, (gcdTailStep (model := model) output entry.1).2)))) := by
  simp only [gcdTail, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    NumberTheory.GCD.gcdLexical_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem loadTail_execute (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (Circuit.seq (ConstantWord.circuit (model := model) (modulusRef ctx N) N)
      (gcdTail (model := model) output)).execute Reference state =
      state.mapClassical (fun entry => ((loadTailStep (model := model) output entry.1).1,
        (entry.2.1, (entry.2.2, (loadTailStep (model := model) output entry.1).2)))) := by
  simp only [ConstantWord.circuit, Circuit.execute_seq, ConstantWord.constantWord_fold_execute,
    gcdTail_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual adjacent arithmetic, literal modulus loading and native GCD compose on full blocks. -/
theorem body_execute (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference (model.HiddenState × History)) :
    (body (model := model) successor halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((bodyStep (model := model) successor halfPower
        output entry.1).1,
        (entry.2.1, (entry.2.2, (bodyStep (model := model) successor halfPower output
          entry.1).2)))) := by
  unfold body
  rw [Circuit.execute_seq, loadTail_execute, NativeAdjacentWord.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem inner_execute (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (adjacentContext ctx N) Reference (model.HiddenState × History)) :
    (Circuit.workspace (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body (model := model) successor halfPower output)).execute Reference state =
      state.mapClassical (fun entry => ((innerStep (model := model) successor halfPower
        output entry.1).1,
        (entry.2.1, (entry.2.2, (innerStep (model := model) successor halfPower output
          entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical (adjacentContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
    (body (model := model) successor halfPower output)
    (fun entry =>
      let next := bodyStep (model := model) successor halfPower output entry.1
      ((next.1, entry.2), next.2))
    (fun reference {_} _ initial => by
      refine (body_execute successor halfPower output reference initial).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The real complete GCD call releases precisely its two outer operand cells. -/
theorem code_execute (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) successor halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((step (model := model) successor halfPower output
        entry.1).1,
        (entry.2.1, (entry.2.2, (step (model := model) successor halfPower output entry.1).2))))
          := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body (model := model) successor halfPower output))
    (fun entry =>
      let next := innerStep (model := model) successor halfPower output entry.1
      ((next.1, entry.2), next.2))
    (fun reference {_} _ initial => by
      refine (inner_execute successor halfPower output reference initial).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
