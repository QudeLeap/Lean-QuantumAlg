/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Quadratic
import all QuantumAlg.Core.Execution.Instrument.Recorded.Feed
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Step

/-!
# Raw-vector quadratics of an actual source stage

The two instruments describe the actual reset and measured middle. Their
mathematical source feed changes only the observation space. Every original
record and both actual Paths survive, including a changed service state.
The vector need not have unit norm and no intermediate branch is normalized.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution
open scoped BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {FirstOutcome LastOutcome : Type}
  [Fintype FirstOutcome] [Fintype LastOutcome]
  {first last : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
    services).Environment}

private lemma sourceStep_recorded_quadratic_pure
    (head : Instrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × ((History × first.Path) × last.Path)))
    (vector : NormalizedVector (ctx.register.prod Reference)) :
    HilbertOperator.quadraticWeight
        (stepObservable Reference feed first last environment effects original).matrix vector =
      ∑ firstOutcome : FirstOutcome, ∑ lastOutcome : LastOutcome,
        HilbertOperator.quadraticWeight
          (effects (sourceFullRetainedRecord tail.record
            (Instrument.retainedRecord (services := services) head.record original firstOutcome)
              lastOutcome)).matrix
          ((recordedFeedOperator head tail Reference feed (original.1, original.2.1)
            firstOutcome lastOutcome).applyVec vector) := by
  let : Fintype History := Fintype.ofFinite History
  exact retained_quadratic_pure_two
    (Original := Store ctx × (services.HiddenState × History))
    (First := FirstOutcome) (Last := LastOutcome)
    (Result := Store ctx × (services.HiddenState × ((History × first.Path) × last.Path)))
    (R := ctx.register.prod Reference) (Classical.decEq _)
    (fun state => last.execute environment Reference
      ((first.execute environment Reference state).applyUnitary (fun _ => feed)))
    (fun incoming firstOutcome lastOutcome =>
      sourceFullRetainedRecord tail.record
        (Instrument.retainedRecord (services := services) head.record incoming firstOutcome)
          lastOutcome)
    (fun incoming firstOutcome lastOutcome =>
      recordedFeedOperator head tail Reference feed (incoming.1, incoming.2.1)
        firstOutcome lastOutcome)
    effects (stepObservable Reference feed first last environment effects)
    (recorded_feed_blocks head tail Reference feed)
    (window_sourceStep_state_weight Reference feed first last environment effects) original vector

/-- The actual single-stage pullback is the exact sum on all retained raw-vector fibers. -/
lemma window_sourceStep_recorded_quadratic (head : Instrument first FirstOutcome environment)
    (tail : RecordedInstrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × ((History × first.Path) × last.Path)))
    (vector : HilbertVector (ctx.register.prod Reference)) :
    HilbertOperator.quadraticWeight
        (stepObservable Reference feed first last environment effects original).matrix vector =
      ∑ firstOutcome : FirstOutcome, ∑ lastOutcome : LastOutcome,
        HilbertOperator.quadraticWeight
          (effects (sourceFullRetainedRecord tail.record
            (Instrument.retainedRecord (services := services) head.record original firstOutcome)
              lastOutcome)).matrix
          ((recordedFeedOperator head tail Reference feed (original.1, original.2.1)
            firstOutcome lastOutcome).applyVec vector) := by
  exact quadratic_sum_two_of_normalized
    (stepObservable Reference feed first last environment effects original).matrix
    (fun firstOutcome lastOutcome =>
      (effects (sourceFullRetainedRecord tail.record
        (Instrument.retainedRecord (services := services) head.record original firstOutcome)
          lastOutcome)).matrix)
    (fun firstOutcome lastOutcome =>
      recordedFeedOperator head tail Reference feed (original.1, original.2.1)
        firstOutcome lastOutcome)
    (sourceStep_recorded_quadratic_pure head tail Reference feed original effects) vector

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
