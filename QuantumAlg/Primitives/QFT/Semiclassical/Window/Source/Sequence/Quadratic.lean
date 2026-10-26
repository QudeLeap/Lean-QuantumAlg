/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Step.Quadratic

/-!
# Coherent raw-vector observations of a complete actual source sequence

Each stage carries certificates of its original reset and measured middle.
The recursive finite sums retain their literal intermediate Stores, service
states, actual Paths and incoming History. A coherent input is transformed
as one vector throughout; there is no sum of basis-state probabilities.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution
open scoped BigOperators

namespace Stage

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

/-- Actual component certificates; the source feed is not a physical circuit certificate. -/
structure Instruments (stage : Stage ctx operations services Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) where
  FirstOutcome : Type
  firstFinite : Fintype FirstOutcome
  LastOutcome : Type
  lastFinite : Fintype LastOutcome
  head : letI := firstFinite; Instrument stage.first FirstOutcome environment
  tail : letI := lastFinite; RecordedInstrument stage.last LastOutcome environment

/-- Component certificates for the same ordered actual stage list. -/
def Certificates
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) : List (Stage ctx operations services Reference) → Type 1
  | [] => ULift.{1} Unit
  | stage :: rest => Instruments stage environment × Certificates environment rest

/-- Exact recursive quadratics of all actual outcomes, retaining the complete raw vector. -/
def quadraticSum
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) :
    (stages : List (Stage ctx operations services Reference)) →
      Certificates environment stages → {History : Type} →
      Circuit.EffectFamily ctx Reference (services.HiddenState × Records stages History) →
      Store ctx × (services.HiddenState × History) →
      HilbertVector (ctx.register.prod Reference) → Real
  | [], _, _, effects, original, vector =>
      HilbertOperator.quadraticWeight (effects original).matrix vector
  | stage :: rest, certificates, _, effects, original, vector =>
      let : Fintype certificates.1.FirstOutcome := certificates.1.firstFinite
      let : Fintype certificates.1.LastOutcome := certificates.1.lastFinite
      ∑ firstOutcome : certificates.1.FirstOutcome,
        ∑ lastOutcome : certificates.1.LastOutcome,
          quadraticSum environment rest certificates.2 effects
            (sourceFullRetainedRecord certificates.1.tail.record
              (Instrument.retainedRecord (services := services)
                certificates.1.head.record original firstOutcome) lastOutcome)
            ((recordedFeedOperator certificates.1.head certificates.1.tail Reference stage.feed
              (original.1, original.2.1) firstOutcome lastOutcome).applyVec vector)

/-- Structural list induction connects all coherent outcome sums to the original effect. -/
lemma window_sourceSequence_quadratic
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (stages : List (Stage ctx operations services Reference))
    (certificates : Certificates environment stages)
    {History : Type} [Finite History]
    (effects : Circuit.EffectFamily ctx Reference (services.HiddenState × Records stages History))
    (original : Store ctx × (services.HiddenState × History))
    (vector : HilbertVector (ctx.register.prod Reference)) :
    HilbertOperator.quadraticWeight
        (observation environment stages effects original).matrix vector =
      quadraticSum environment stages certificates effects original vector := by
  induction stages generalizing History vector with
  | nil => rfl
  | cons stage rest ih =>
      let : Fintype certificates.1.FirstOutcome := certificates.1.firstFinite
      let : Fintype certificates.1.LastOutcome := certificates.1.lastFinite
      change HilbertOperator.quadraticWeight
        (stepObservable Reference stage.feed stage.first stage.last environment
          (observation environment rest effects) original).matrix vector = _
      rw [window_sourceStep_recorded_quadratic certificates.1.head certificates.1.tail]
      change (∑ firstOutcome : certificates.1.FirstOutcome,
        ∑ lastOutcome : certificates.1.LastOutcome, _) =
          ∑ firstOutcome : certificates.1.FirstOutcome,
            ∑ lastOutcome : certificates.1.LastOutcome, _
      apply Finset.sum_congr rfl
      intro firstOutcome _
      apply Finset.sum_congr rfl
      intro lastOutcome _
      exact ih certificates.2 effects _ _

end Stage

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
