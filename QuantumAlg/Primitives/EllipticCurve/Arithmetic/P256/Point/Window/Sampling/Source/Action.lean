/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Correctness.Affine
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Scalars

/-!
# The actual named window on a complete source column

The same measured driver is followed by its real Fourier row. Every actual
outcome has the original arithmetic coefficient, the recorded Fourier phase,
and the complete next zero-bank physical label beside the remaining source.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumAlg.Execution.Instrument

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] Driver.namedDriverInstrument
  Locality.namedMeasuredMiddleInstrument sourceFedRaw

/-- The driver's complete physical ket uses exactly the sampler's original placement. -/
lemma namedDriverKetAction_physical (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (first last : Raw) (Reference : Register)
    (reference : Reference.Index)
    (action : Driver.namedDriverKetAction (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row
      environment before first last (Reference := Reference) reference) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ hidden outcome,
      (referenceLift Reference (point.2.2.operator (before, hidden) outcome)).applyVec
          (NormalizedVector.ket (R := ctx.register.prod Reference)
            (parameters.physicalLabel first, reference)).vec =
        (NormalizedVector.invSqrt2 ^ 2048) •
          (NormalizedVector.ket (R := ctx.register.prod Reference)
            (parameters.physicalLabel last, reference)).vec := by
  exact action

/-- The exact complete-reference ket action of the original fed named window. -/
def sourceWindowKetAction (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (source : SourceRegister.Index) (first last : Raw)
    (Reference : Register) (reference : Reference.Index) : Prop :=
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      (referenceLift (SourceRegister.prod Reference)
          ((Locality.namedMeasuredMiddleInstrument parameters index environment).operator
            (before, hidden) (pointOutcome, outcome))).applyVec
        ((parameters.sourceFeed index Reference).applyVec
          (NormalizedVector.ket (R := ctx.register.prod (SourceRegister.prod Reference))
            (parameters.physicalLabel first,
              remainingSource index.sourceStart source, reference)).vec) =
      windowScalar parameters index before source outcome •
        (NormalizedVector.ket (R := ctx.register.prod (SourceRegister.prod Reference))
          (parameters.physicalLabel last,
            remainingSource index.sourceEnd source, reference)).vec

/-- All point and Fourier outcomes return the same complete next boundary ket. -/
private def NamedWindowSourceKetStatement : Prop :=
  ∀ (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (hidden : services.HiddenState)
    (source : SourceRegister.Index) (first last : Raw)
    (_firstZero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits (parameters.physicalLabel first)).1 =
        Partner.zeroBits (index.lowerWidth + 1))
    (_lastZero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits (parameters.physicalLabel last)).1 =
        Partner.zeroBits (index.lowerWidth + 1))
    (Reference : Register) (reference : Reference.Index)
    (_pointAction : Driver.namedDriverKetAction (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row
      environment before (sourceFedRaw parameters index source first)
      (sourceFedRaw parameters index source last)
      (Reference := SourceRegister.prod Reference)
      (remainingSource index.sourceEnd source, reference)),
    sourceWindowKetAction parameters index environment before hidden source first last
      Reference reference

private lemma namedWindowSourceKetStatement_proof :
    NamedWindowSourceKetStatement (ctx := ctx) (services := services) := by
  unfold NamedWindowSourceKetStatement
  intro parameters index environment before hidden source first last firstZero lastZero
    Reference reference pointAction
  unfold sourceWindowKetAction
  let chosen := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype chosen.1 := chosen.2.1
  dsimp only
  intro pointOutcome outcome
  have point := namedDriverKetAction_physical parameters index environment before
    (sourceFedRaw parameters index source first) (sourceFedRaw parameters index source last)
    (SourceRegister.prod Reference) (remainingSource index.sourceEnd source, reference)
    pointAction hidden pointOutcome
  let column : (ctx.register.prod (SourceRegister.prod Reference)).Index :=
    (parameters.physicalLabel first, remainingSource index.sourceStart source, reference)
  let target : (ctx.register.prod (SourceRegister.prod Reference)).Index :=
    (parameters.physicalLabel (sourceFedRaw parameters index source last),
      remainingSource index.sourceEnd source, reference)
  have action := Locality.namedMeasuredMiddle_feed_ket parameters index environment Reference
    (before, hidden) pointOutcome outcome
    column target (NormalizedVector.invSqrt2 ^ 2048) (by
      rw [sourceFeed_original_column parameters index Reference first source reference firstZero]
      exact point)
  unfold Locality.measuredMiddleFeedKetAction at action
  have feedback := parameters.named_point_feedback_scalar index environment
    (before, hidden) pointOutcome
    (parameters.physicalLabel (sourceFedRaw parameters index source last))
  unfold RecordedFeedbackScalar at feedback
  rw [fedRaw_frequency, feedback, sourceFedRaw_bank,
    zeroBank_fedRaw parameters index Reference source last
      (remainingSource index.sourceEnd source) reference lastZero] at action
  exact action

/-- All point and Fourier outcomes return the same complete next boundary ket. -/
lemma named_window_source_ket (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (before : Store ctx) (hidden : services.HiddenState)
    (source : SourceRegister.Index) (first last : Raw)
    (firstZero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits (parameters.physicalLabel first)).1 =
        Partner.zeroBits (index.lowerWidth + 1))
    (lastZero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits (parameters.physicalLabel last)).1 =
        Partner.zeroBits (index.lowerWidth + 1))
    (Reference : Register) (reference : Reference.Index)
    (pointAction : Driver.namedDriverKetAction (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row
      environment before (sourceFedRaw parameters index source first)
      (sourceFedRaw parameters index source last)
      (Reference := SourceRegister.prod Reference)
      (remainingSource index.sourceEnd source, reference)) :
    sourceWindowKetAction parameters index environment before hidden source first last
      Reference reference := by
  have action := namedWindowSourceKetStatement_proof (ctx := ctx) (services := services)
  unfold NamedWindowSourceKetStatement at action
  exact action parameters index environment before hidden source first last firstZero lastZero
    Reference reference pointAction

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
