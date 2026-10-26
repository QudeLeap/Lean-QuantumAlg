/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Feed
import all QuantumAlg.Core.Execution.Instrument.Recorded

/-!
# Complete retained blocks around a mathematical unitary feed

The feed is a unitary on the observation space between two actual circuit
interpreters. It introduces no physical instruction or path. Both actual
records, the exact intermediate Store, service state, and incoming history
remain in the same density fibers.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {FirstOutcome LastOutcome : Type}
  [Fintype FirstOutcome] [Fintype LastOutcome]
  {first last : Circuit (.quantum gates oracles operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- The final Kraus factor reads exactly the first component's returned Store and service state. -/
def recordedFeedOperator (head : Instrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (original : Store ctx × services.HiddenState)
    (firstOutcome : FirstOutcome) (lastOutcome : LastOutcome) :
    HilbertOperator (ctx.register.prod Reference) :=
  referenceLift Reference
      (tail.operator ((head.record original.1 firstOutcome).1, original.2) lastOutcome) *
    ((feed : HilbertOperator (ctx.register.prod Reference)) *
      referenceLift Reference (head.operator original.1 firstOutcome))

/-- Exact complete blocks of the real reset, mathematical feed and actual allocating middle. -/
lemma recorded_feed_blocks (head : Instrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × ((History × first.Path) × last.Path))) :
    ((last.execute environment Reference
      ((first.execute environment Reference state).applyUnitary (fun _ => feed))
        ).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ firstOutcome : FirstOutcome, ∑ lastOutcome : LastOutcome,
          if sourceFullRetainedRecord tail.record
              (retainedRecord (services := services) head.record original firstOutcome)
                lastOutcome = result then
            recordedFeedOperator head tail Reference feed (original.1, original.2.1)
                firstOutcome lastOutcome *
              (state.block original).matrix *
                (recordedFeedOperator head tail Reference feed (original.1, original.2.1)
                  firstOutcome lastOutcome).conjTranspose
          else 0 := by
  exact feed_composed_retained_blocks state (first.execute environment Reference state)
    (fun incoming => last.execute environment Reference incoming)
    (retainedRecord (services := services) head.record)
    (sourceFullRetainedRecord tail.record)
    (fun original outcome => referenceLift Reference (head.operator original.1 outcome))
    (fun middle outcome => referenceLift Reference
      (tail.operator (middle.1, middle.2.1) outcome))
    (fun selected => (head.blocks Reference state selected).trans
      (sum_condition_decisions _ _ _ _))
    (fun incoming selected => (tail.blocks Reference incoming selected).trans
      (sum_condition_decisions _ _ _ _)) feed result

/-- The mathematical feed remains between the two actual retained operator actions. -/
lemma recordedFeedOperator_applyVec
    (head : Instrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (original : Store ctx × services.HiddenState)
    (a : FirstOutcome) (b : LastOutcome)
    (vector : HilbertVector (ctx.register.prod Reference)) :
    (recordedFeedOperator head tail Reference feed original a b).applyVec vector =
      (referenceLift Reference
        (tail.operator ((head.record original.1 a).1, original.2) b)).applyVec
        (HilbertOperator.applyVec (feed : HilbertOperator (ctx.register.prod Reference))
          ((referenceLift Reference (head.operator original.1 a)).applyVec vector)) := by
  rw [recordedFeedOperator, HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]

/-- Raw-vector scalar actions retain the exact intermediate Store and service state. -/
lemma recorded_feed_reference_applyVec
    (head : Instrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    (original : Store ctx × services.HiddenState)
    (a : FirstOutcome) (b : LastOutcome)
    (initial middle fed final : HilbertVector (ctx.register.prod Reference))
    (firstScalar lastScalar : Complex)
    (headAction : (referenceLift Reference (head.operator original.1 a)).applyVec initial =
      firstScalar • middle)
    (feedAction : HilbertOperator.applyVec
      (feed : HilbertOperator (ctx.register.prod Reference)) middle = fed)
    (tailAction : (referenceLift Reference
      (tail.operator ((head.record original.1 a).1, original.2) b)).applyVec fed =
        lastScalar • final) :
    (recordedFeedOperator head tail Reference feed original a b).applyVec initial =
      (firstScalar * lastScalar) • final := by
  rw [recordedFeedOperator_applyVec, headAction, HilbertOperator.applyVec_smul, feedAction,
    HilbertOperator.applyVec_smul, tailAction, smul_smul]

end

end QuantumAlg.Execution
