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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The real result initialization precedes the existing Euclidean record. -/
def gcdTailStep (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) : Store (context ctx N) × (gcdTail output).Path :=
  let next := NumberTheory.GCD.lexicalStep (operands ctx N) (liftWrite output)
    (store.applyOp (clearOp output))
  (next.1, ((), next.2))

/-- The literal modulus-load record feeds its actual written word to the GCD. -/
def loadTailStep (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) : Store (context ctx N) ×
      (Circuit.seq (ConstantWord.circuit (modulusRef ctx N) N) (gcdTail output)).Path :=
  let loaded := ConstantWord.foldStep (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) store
  let reduced := gcdTailStep output loaded.1
  (reduced.1, (loaded.2, reduced.2))

/-- The first real adjacent-word result is the operand read by the following actual GCD. -/
def bodyStep (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) : Store (context ctx N) ×
      (body successor halfPower output).Path :=
  let adjacent := NativeAdjacentWord.step successor (liftInput halfPower) (adjacentRef ctx N) store
  let reduced := loadTailStep output adjacent.1
  (reduced.1, (adjacent.2, reduced.2))

/-- Enter and release the actual modulus operand around the same physical body. -/
def innerStep (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (adjacentContext ctx N)) : Store (adjacentContext ctx N) ×
      (body successor halfPower output).Path :=
  let next := bodyStep successor halfPower output
    (store.pushWorkspace (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh)
  (Store.popWorkspace (adjacentContext ctx N).canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh next.1,
    next.2)

/-- Both real operand scopes return the actual GCD store and path to the original context. -/
def step (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) (store : Store ctx) :
    Store ctx × (code successor halfPower output).Path :=
  let next := innerStep successor halfPower output
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (modulusBits N + 1))
    ctx.canonicalFreshKey_fresh next.1, next.2)

private theorem gcdTail_execute (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (gcdTail output).execute Reference state =
      state.mapClassical (fun entry => ((gcdTailStep output entry.1).1,
        (entry.2, (gcdTailStep output entry.1).2))) := by
  have actual := Circuit.execute_seq_mapClassical (.classical (clearOp output))
    (NumberTheory.GCD.lexicalBody (operands ctx N) (liftWrite output))
    (fun store => (store.applyOp (clearOp output), ()))
    (NumberTheory.GCD.lexicalStep (operands ctx N) (liftWrite output))
    (fun reference {_} _ initial => by
      simpa only [Circuit.mapClassical_canonicalDecision] using
        Circuit.execute_classical_mapClassical (clearOp output) reference initial)
    (NumberTheory.GCD.gcdLexical_execute (operands ctx N) (liftWrite output)) Reference state
  refine actual.trans ?_
  exact congrArg
    (fun decision : DecidableEq (Store (context ctx N) × (History × (gcdTail output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((gcdTailStep output entry.1).1,
          (entry.2, (gcdTailStep output entry.1).2)))) (Subsingleton.elim _ _)

private theorem loadTail_execute (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (Circuit.seq (ConstantWord.circuit (modulusRef ctx N) N) (gcdTail output)).execute
        Reference state =
      state.mapClassical (fun entry => ((loadTailStep output entry.1).1,
        (entry.2, (loadTailStep output entry.1).2))) := by
  have actual := Circuit.execute_seq_mapClassical (ConstantWord.circuit (modulusRef ctx N) N)
    (gcdTail output)
    (ConstantWord.foldStep (modulusRef ctx N)
      (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)))
    (gcdTailStep output)
    (ConstantWord.constantWord_fold_execute (modulusRef ctx N)
      (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)))
    (gcdTail_execute output) Reference state
  simpa only [loadTailStep, Circuit.mapClassical_canonicalDecision] using actual

/-- Actual adjacent arithmetic, literal modulus loading and native GCD compose on full blocks. -/
theorem body_execute (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx N) Reference History) :
    (body successor halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((bodyStep successor halfPower output entry.1).1,
        (entry.2, (bodyStep successor halfPower output entry.1).2))) := by
  have actual := Circuit.execute_seq_mapClassical
    (NativeAdjacentWord.code successor (liftInput halfPower) (adjacentRef ctx N))
    (.seq (ConstantWord.circuit (modulusRef ctx N) N) (gcdTail output))
    (NativeAdjacentWord.step successor (liftInput halfPower) (adjacentRef ctx N))
    (loadTailStep output)
    (NativeAdjacentWord.code_execute successor (liftInput halfPower) (adjacentRef ctx N))
    (loadTail_execute output) Reference state
  refine actual.trans ?_
  exact congrArg
    (fun decision : DecidableEq
        (Store (context ctx N) × (History × (body successor halfPower output).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod (context ctx N).register Reference)
        decision state (fun entry => ((bodyStep successor halfPower output entry.1).1,
          (entry.2, (bodyStep successor halfPower output entry.1).2)))) (Subsingleton.elim _ _)

/-- The real complete GCD call releases precisely its two outer operand cells. -/
theorem code_execute (successor : Bool) (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code successor halfPower output).execute Reference state =
      state.mapClassical (fun entry => ((step successor halfPower output entry.1).1,
        (entry.2, (step successor halfPower output entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord (modulusBits N + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (adjacentContext ctx N) (adjacentContext ctx N).canonicalFreshKey
      (.unsignedWord (modulusBits N + 1)) (adjacentContext ctx N).canonicalFreshKey_fresh
      (body successor halfPower output))
    (innerStep successor halfPower output)
    (fun reference {history} _ initial => by
      have inner := Circuit.execute_workspace_mapClassical
        (adjacentContext ctx N).canonicalFreshKey (.unsignedWord (modulusBits N + 1))
        (adjacentContext ctx N).canonicalFreshKey_fresh (body successor halfPower output)
        (bodyStep successor halfPower output) (body_execute successor halfPower output)
        reference initial
      refine inner.trans ?_
      exact congrArg
        (fun decision : DecidableEq
            (Store (adjacentContext ctx N) × (history × (body successor halfPower output).Path)) =>
          @ExecutionState.mapClassical _ _ _ _
            (Register.prod (adjacentContext ctx N).register reference) decision initial
            (fun entry => ((innerStep successor halfPower output entry.1).1,
              (entry.2, (innerStep successor halfPower output entry.1).2))))
        (Subsingleton.elim _ _))
    Reference state).trans ?_
  exact (Circuit.mapClassical_canonicalDecision _ state
    (fun entry => ((step successor halfPower output entry.1).1,
      (entry.2, (step successor halfPower output entry.1).2)))).trans
    (Circuit.mapClassical_canonicalDecision _ state
      (fun entry => ((step successor halfPower output entry.1).1,
        (entry.2, (step successor halfPower output entry.1).2)))).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
