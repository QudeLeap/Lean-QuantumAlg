/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Semantics

/-!
# Complete caller frame of actual candidate verification

All four original stages write only the scalar accumulator and the point
acceptance cell. Every other structural input retains its full value on every
raw input, including failure flags and noncanonical point encodings. Fresh
placement can therefore preserve the complete original caller context.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- Each actual caller read outside the two verification destinations is bitwise unchanged. -/
theorem verifyStep_preserves_read {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (store : Store ctx) (hidden : model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (scalarFree : scalarResult.key ∉ observed.storageKeys)
    (acceptedFree : accepted.key ∉ observed.storageKeys) :
    (verifyStep spec candidate base target inverseSuccess reconstruction
      scalarResult accepted (store, hidden)).1.1.read observed =
        store.read observed := by
  rw [verifyStep_store]
  exact (Store.read_applyOp_of_not_mem_storageKeys _
    (conjunctionOp reconstruction accepted) observed acceptedFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys _ (conjunctionOp inverseSuccess accepted)
      observed acceptedFree).trans
      ((PointEquality.Native.compareInto_preserves_read _ target accepted _
        observed acceptedFree).trans
        (ScalarMul.Native.scalarStep_preserves_read spec (candidateBits candidate)
          base scalarResult (store, hidden) observed scalarFree)))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
