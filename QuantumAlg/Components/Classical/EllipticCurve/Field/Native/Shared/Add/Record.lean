/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add.Semantics

/-!
# Reusable actual shared-modulus addition record

This record describes the already-constructed five-operation program. Its
proof choice does not enter circuit construction, operand references or
native labels. Caller stores and arbitrary Reference use the same record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Certified record of the actual allocated addition and scratch releases. -/
def addIntoWordStep (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (addIntoWord (model := model) left right modulus output).Path :=
  Classical.choose (addIntoWord_actualRecord (environment := environment) left right modulus output)

/-- The actual record describes every original joint input and chronological history. -/
lemma sharedAddIntoWord_execute (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (addIntoWord (model := model) left right modulus output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := addIntoWordStep (environment := environment) left right modulus output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  (Classical.choose_spec (addIntoWord_actualRecord (environment := environment)
    left right modulus output)).1 Reference state

/-- Only the caller result is overwritten; both operand aliases and all other cells are retained. -/
lemma sharedAddIntoWordStep_store (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (addIntoWordStep (environment := environment) left right modulus output store).1 =
      store.write output (addValue (store.read left) (store.read right) (store.read modulus)) :=
  (Classical.choose_spec (addIntoWord_actualRecord (environment := environment)
    left right modulus output)).2 store

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared
