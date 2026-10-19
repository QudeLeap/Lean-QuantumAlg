/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public.Semantics

/-!
# Original acceptance of the actual public XGCD result

The existing public result tuple is read from the actual returned store.
Its original acceptance relation includes the gcd, Bezout equation and both
original public coefficient ranges, on the complete total operand domain.
No additional arithmetic or output conversion is executed by this theorem.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- One actual state-path record returns a tuple satisfying the original total XGCD relation. -/
lemma xgcdNativePublicIntoResult_accepts
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (publicIntoResult (model := model) input result).execute environment Reference state =
          state.mapClassical (fun entry =>
            let actual := record (entry.1, entry.2.1)
            (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        let value := decodeXGCDTuple ((record before).1.1.read (GCD.cellRead result))
        PureXGCD.accepts (GCD.decodeOperands (before.1.read input))
          ⟨value.1, value.2.1, value.2.2⟩ := by
  obtain ⟨record, equation, correct⟩ := xgcdNativePublicIntoResult_actualRecord input result
  refine ⟨record, equation, ?_⟩
  intro before
  dsimp only
  rw [correct before]
  simp only [GCD.cellRead, Store.read_write_same, decode_encode_xgcdTuple]
  exact PureXGCD.xgcdEval_accepts (GCD.decodeOperands (before.1.read input))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
