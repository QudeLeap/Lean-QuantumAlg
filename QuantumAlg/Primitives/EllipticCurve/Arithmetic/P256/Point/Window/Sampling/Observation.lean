/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Step
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Stream

/-!
# Actual measured-window source observations on the complete exponent square

Every window uses the same mathematical pair of full exponent labels.
The source feed is an observation-space operator only, never an allocated
physical bank. The surrounding reset and measured five-table Driver are
their actual interpreters, retaining complete Store/HiddenState/History/Path
and arbitrary Reference. Positive contraction holds on every label; no
good-branch point-character or Born assertion is made by this component.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

/-- Mathematical source coordinates only; these are never physically allocated by the sampler. -/
abbrev SourceRegister : Register := (Qubits 260).prod (Qubits 260)

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

variable (parameters : Parameters ctx)

/-- The exact actual paid-table measured middle and same-bank corrected inverse word. -/
def measuredMiddle (index : WindowIndex) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  (Driver.circuit (parameters.pointParameters index) parameters.frame parameters.modulus
    index.row).seq
      (QuantumFourierTransform.Semiclassical.Window.liftedInverse (parameters.ports index))

/-- Select original stream exponent bits from the same mathematical pair for every window. -/
def sourcePartition (index : WindowIndex) :
    SourceRegister.Index ≃ (Qubits (index.lowerWidth + 1)).Index ×
      (labelRemainder (streamPositions (parameters.ports index))).Index :=
  (prodEquiv (m := 260) (n := 260)).trans
    (labelPartition (streamPositions (parameters.ports index)))

/-- Mathematical feed retains every physical complement and external Reference. -/
def sourceFeed (index : WindowIndex) (Reference : Register) :
    UnitaryOperator (ctx.register.prod (SourceRegister.prod Reference)) :=
  selectedFeedOperator (S := SourceRegister)
    (Rest := labelRemainder (streamPositions (parameters.ports index)))
    (parameters.ports index) (parameters.sourcePartition index) Reference

/-- Actual reset and measured middle give a positive contraction on all labels. -/
def sourceObservation (index : WindowIndex) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (effects : Circuit.EffectFamily ctx (SourceRegister.prod Reference)
      (services.HiddenState × ((History × (parameters.reset (services := services) index).Path) ×
        (parameters.measuredMiddle (services := services) index).Path))) :
    Circuit.EffectFamily ctx (SourceRegister.prod Reference)
      (services.HiddenState × History) :=
  stepObservable (SourceRegister.prod Reference) (parameters.sourceFeed index Reference)
    (parameters.reset (services := services) index)
    (parameters.measuredMiddle (services := services) index) environment effects

/-- Exact actual full-record weight of this concrete reset/feed/measured-Driver composition. -/
lemma sourceObservation_state_weight (index : WindowIndex) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (effects : Circuit.EffectFamily ctx (SourceRegister.prod Reference)
      (services.HiddenState × ((History × (parameters.reset (services := services) index).Path) ×
        (parameters.measuredMiddle (services := services) index).Path)))
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History)) :
    ((parameters.measuredMiddle (services := services) index).execute environment
      (SourceRegister.prod Reference)
      (ExecutionState.applyUnitary
        ((parameters.reset (services := services) index).execute environment
          (SourceRegister.prod Reference) state)
        (fun _ => parameters.sourceFeed index Reference))).effectWeight effects =
      state.effectWeight (parameters.sourceObservation index Reference environment effects) :=
  window_sourceStep_state_weight (SourceRegister.prod Reference)
    (parameters.sourceFeed index Reference) (parameters.reset (services := services) index)
    (parameters.measuredMiddle (services := services) index) environment effects state

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
