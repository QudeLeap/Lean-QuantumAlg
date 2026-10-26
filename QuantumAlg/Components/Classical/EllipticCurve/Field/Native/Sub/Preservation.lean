/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Structural reads outside the actual paid subtraction destination

The paid native subtraction has a complete Store certificate: after releasing
its lexical scratch, exactly its declared output is written.  This lemma
turns that certificate into a reusable preservation rule for other inputs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- A structural read disjoint from the signed output survives the real paid subtraction. -/
lemma subIntoWordStep_read_other
    (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (input : CInputRef ctx shape)
    (separate : output.key ∉ input.storageKeys) :
    (subIntoWordStep (model := model) (environment := environment)
      spec left right output store).1.read input = store.read input := by
  rw [subIntoWordStep_store]
  exact Store.read_write_of_not_mem_storageKeys store output
    (subtractionWord spec (store.read left) (store.read right)) input separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
