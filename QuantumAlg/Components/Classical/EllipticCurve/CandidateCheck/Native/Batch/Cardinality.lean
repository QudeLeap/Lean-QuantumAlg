/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.TailResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality

/-!
# Original numerical ceiling for the actual allocated recovery tail

The seven persistent destinations are retained once, every declared attempt
executes, and the final eighth retained result is packed once. The numerical
ceiling counts the same actual native pool, including the final pack when no
attempts are declared.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- The original independent pool contains every attempt allowance and exactly one final pack. -/
lemma recoveryTailEnvelope_card (model : ExecutionModel) [BitWord.Selected model]
    (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth) (count : Nat) :
    (recoveryTailEnvelope model curve modulus count).card =
      count * (attemptEnvelope model curve modulus).card + 1 := by
  simp only [recoveryTailEnvelope, repeatedAttemptsEnvelope, ResourcePool.scale,
    Multiset.card_add, Multiset.card_nsmul]
  rfl

/-- All actual stages retain the original complete batch numerical event ceiling. -/
lemma recoveryTailEnvelope_card_le (model : ExecutionModel) [BitWord.Selected model]
    (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth) (count : Nat) :
    (recoveryTailEnvelope model curve modulus count).card ≤
      count * (42 * scalarWidth + scalarWidth * (248 * width + 644) + 119) + 1 := by
  rw [recoveryTailEnvelope_card]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left count (attemptEnvelope_card_le model curve modulus)) 1

/-- Every actual allocated tail path satisfies that same original complete numerical ceiling. -/
lemma recoveryTail_eventCount_le (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (path : (recoveryTail curve modulus samples base target).Path) :
    ((recoveryTail curve modulus samples base target).eventTrace path).length ≤
      count * (42 * scalarWidth + scalarWidth * (248 * width + 644) + 119) + 1 :=
  (Multiset.card_le_card (recoveryTail_pool_le curve modulus samples base target path)).trans
    (recoveryTailEnvelope_card_le model curve modulus count)

/-- With no attempts, the real final retained result still incurs exactly its one pack event. -/
lemma recoveryTail_eventCount_zero (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin 0 → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (path : (recoveryTail curve modulus samples base target).Path) :
    ((recoveryTail curve modulus samples base target).eventTrace path).length = 1 := by
  change ((recoveryBatch curve modulus samples base target).eventTrace path.1 ++
    (packBatchResult ctx width scalarWidth).eventTrace path.2).length = 1
  rw [recoveryBatch_eventTrace, packBatchResult_eventTrace]
  rfl

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
