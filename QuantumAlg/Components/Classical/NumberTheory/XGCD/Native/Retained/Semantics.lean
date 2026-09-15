/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Retained
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public.Semantics
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Complete retained XGCD execution and original total output

One actual record preserves every quantum-reference block and original caller
cell while retaining the exact original deterministic result. Initialization,
internal separation and signed ranges are already supplied by the actual
public body; the external caller supplies only a fresh result destination.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual retention and execution return one initialized-and-written complete caller store. -/
theorem xgcdNativeRetained_actualRecord
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx →
        Store (retainedCtx ctx width key fresh) × (retainedCircuit input key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (retainedCircuit input key fresh).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 =
        (before.pushRetained key (XGCDOutputShape width) fresh).write
          (CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh)
          (encodeXGCDTuple ((PureXGCD.eval (GCD.decodeOperands (before.read input))).gcd,
            ((PureXGCD.eval (GCD.decodeOperands (before.read input))).leftCoefficient,
              (PureXGCD.eval (GCD.decodeOperands (before.read input))).rightCoefficient))) := by
  let lifted := input.underRetained key (XGCDOutputShape width) fresh
  let output := CWriteRef.retainedHead ctx key (XGCDOutputShape width) fresh
  obtain ⟨bodyRecord, bodyEquation, bodyCorrect⟩ :=
    xgcdNativePublicIntoResult_actualRecord lifted output
  let record (before : Store ctx) :=
    let final := bodyRecord (before.pushRetained key (XGCDOutputShape width) fresh)
    (final.1, ((), final.2))
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    refine (Circuit.execute_retain_seq_mapClassical ctx key (XGCDOutputShape width) fresh
      (publicIntoResult lifted output) bodyRecord bodyEquation reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  · intro before
    have actual := bodyCorrect (before.pushRetained key (XGCDOutputShape width) fresh)
    rw [show (before.pushRetained key (XGCDOutputShape width) fresh).read lifted =
      before.read input from Store.read_pushRetained_underRetained before key
        (XGCDOutputShape width) fresh input] at actual
    exact actual

/-- The retained tuple satisfies the original gcd, Bezout and public signed-range relation. -/
theorem xgcdNativeRetained_accepts
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    ∃ record : Store ctx →
        Store (retainedCtx ctx width key fresh) × (retainedCircuit input key fresh).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (retainedCircuit input key fresh).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        let value := decodeXGCDTuple ((record before).1.read (retainedRead ctx width key fresh))
        PureXGCD.accepts (GCD.decodeOperands (before.read input))
          ⟨value.1, value.2.1, value.2.2⟩ := by
  obtain ⟨record, equation, correct⟩ := xgcdNativeRetained_actualRecord input key fresh
  refine ⟨record, equation, ?_⟩
  intro before
  dsimp only
  rw [correct before]
  simp only [retainedRead]
  exact PureXGCD.xgcdEval_accepts (GCD.decodeOperands (before.read input))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
