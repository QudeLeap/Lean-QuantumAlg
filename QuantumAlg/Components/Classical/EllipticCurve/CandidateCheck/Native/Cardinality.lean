/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Cardinality

/-!
# Original numerical ceiling for actual candidate verification

The real group-power verifier, eight-operation point comparison and both
original Boolean conjunctions remain separate chronological stages.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The original verification allowance charges the actual scalar, comparison and both flags. -/
lemma verificationEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (spec : CurveSpec width)
    (scalarWidth : Nat) :
    (verificationEnvelope model spec scalarWidth).card ≤
      scalarWidth * (248 * width + 644) + 12 := by
  have scalar := ScalarMul.Native.scalarEnvelope_card_le model spec scalarWidth
  simp only [verificationEnvelope, verificationStageEnvelope, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero,
    Multiset.card_add]
  change (ScalarMul.Native.scalarEnvelope model spec scalarWidth).card + (8 + (1 + 1)) ≤ _
  omega

/-- Every actual target-verification path obeys that same original numerical ceiling. -/
lemma verifyInto_eventCount_le (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (path : (verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).Path) :
    ((verifyInto spec candidate base target inverseSuccess reconstruction
      scalarResult accepted).eventTrace path).length ≤ scalarWidth * (248 * width + 644) + 12 :=
  (Multiset.card_le_card (verifyInto_pool_le spec candidate base target inverseSuccess
    reconstruction scalarResult accepted path)).trans
      (verificationEnvelope_card_le model spec scalarWidth)

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
