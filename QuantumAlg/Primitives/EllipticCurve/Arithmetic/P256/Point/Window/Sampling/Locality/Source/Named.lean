/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Instrument
import all QuantumAlg.Core.Execution.Instrument.Sequence
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Fourier.Instrument
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows.Ket

/-!
# The specified measured point and real Fourier row in one source window

The complete allocating middle uses the original paid Driver followed by
the actual same-bank feedback and corrected readout. Both records and
operators consume the point's real returned Store and service state.
The mathematical source feed contributes no physical instruction or Path.
The conditional ket composition is an internal component interface: its
same-named point action must be supplied by the original arithmetic and
affine-domain proof, rather than by a new public algorithm premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open QuantumAlg.Execution.Instrument

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The exact named point certificate precedes its actual corrected Fourier readout. -/
def namedMeasuredMiddleInstrument (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    RecordedInstrument (ctx := ctx) (operations := BitWord.model) (services := services)
      (parameters.measuredMiddle (services := services) index)
      (point.1 × Bits (index.lowerWidth + 1)) environment := by
  let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
    parameters.frame parameters.modulus index.row environment
  letI : Fintype point.1 := point.2.1
  let readout := fourierInstrument (operations := BitWord.model) (services := services)
    (allowAllocation := true) (parameters.ports index) environment
  exact point.2.2.seq readout.recorded

/-- Both real Paths remain in order, and the readout receives the actual point Store. -/
lemma namedMeasuredMiddle_record (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (original : Store ctx × services.HiddenState) :
    let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ outcomes : point.1 × Bits (index.lowerWidth + 1),
      (namedMeasuredMiddleInstrument parameters index environment).record original outcomes =
        let middle := point.2.2.record original outcomes.1
        let final := inverseStoreRecord (operations := BitWord.model) (services := services)
          (parameters.ports index) middle.1.1 outcomes.2
        ((final.1, middle.1.2), (middle.2, final.2)) := by
  dsimp only
  intro outcomes
  rfl

/-- The actual local operator is the same Fourier row times the specified point operator. -/
lemma namedMeasuredMiddle_operator (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (original : Store ctx × services.HiddenState) :
    let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ outcomes : point.1 × Bits (index.lowerWidth + 1),
      (namedMeasuredMiddleInstrument parameters index environment).operator original outcomes =
        inverseLocalOperator (parameters.ports index)
            (point.2.2.record original outcomes.1).1.1 outcomes.2 *
          point.2.2.operator original outcomes.1 := by
  dsimp only
  intro outcomes
  rfl

private lemma selectedFeed_ket {totalBits active : Nat} {S Rest : Register}
    (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (column : (ctx.register.prod (S.prod Reference)).Index) :
    (selectedFeedOperator ports partition Reference).applyVec
        (NormalizedVector.ket column : HilbertVector _) =
      (NormalizedVector.ket (selectedFeedBasis ports partition Reference column) :
        HilbertVector _) := by
  exact UnitaryOperator.ofPerm_applyVec_ket (selectedFeedEquiv ports partition Reference) column

private def measuredMiddleFeedKetAction {totalBits active : Nat} {S Rest : Register}
    (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (operator : HilbertOperator ctx.register) (middle : Store ctx) (outcome : Bits active)
    (column target : (ctx.register.prod (S.prod Reference)).Index) (scalar : Complex) : Prop :=
  (referenceLift (S.prod Reference) operator).applyVec
      ((selectedFeedOperator ports partition Reference).applyVec
        (NormalizedVector.ket column : HilbertVector _)) =
    (scalar * (star (QFTOperator active (decodedWindowFrequency active outcome)
          (binaryEquiv active
            (referenceBankCoordinates ports.wires ports.qubits (S.prod Reference) target).1)) *
        Feedback.wordScalar ports middle target.1 (List.finRange active))) •
      (NormalizedVector.ket (windowZeroBankColumn ports (S.prod Reference) target) :
        HilbertVector _)

private lemma measuredMiddleFeedKetAction_of_eq
    {totalBits active : Nat} {S Rest : Register}
    (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (pointOperator operator : HilbertOperator ctx.register) (middle : Store ctx)
    (outcome : Bits active)
    (column target : (ctx.register.prod (S.prod Reference)).Index) (scalar : Complex)
    (operatorEq : operator = inverseLocalOperator ports middle outcome * pointOperator)
    (pointAction : (referenceLift (S.prod Reference) pointOperator).applyVec
        (NormalizedVector.ket (selectedFeedBasis ports partition Reference column) :
          HilbertVector _) = scalar • (NormalizedVector.ket target : HilbertVector _)) :
    measuredMiddleFeedKetAction ports partition Reference operator middle outcome
      column target scalar := by
  unfold measuredMiddleFeedKetAction
  rw [operatorEq, referenceLift_mul, HilbertOperator.mul_applyVec, selectedFeed_ket,
    pointAction, HilbertOperator.applyVec_smul, window_inverseLocal_reference_ket, smul_smul]

attribute [local irreducible] measuredMiddleFeedKetAction

/-- A proved action of this same named point composes with the real source feed and Fourier row. -/
lemma namedMeasuredMiddle_feed_ket (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register)
    (original : Store ctx × services.HiddenState) :
    let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1))
      (column target : (ctx.register.prod (SourceRegister.prod Reference)).Index) (scalar : ℂ),
      (referenceLift (SourceRegister.prod Reference)
          (point.2.2.operator original pointOutcome)).applyVec
          (NormalizedVector.ket (selectedFeedBasis (parameters.ports index)
            (parameters.sourcePartition index) Reference column) : HilbertVector _) =
        scalar • (NormalizedVector.ket target : HilbertVector _) →
      measuredMiddleFeedKetAction (parameters.ports index) (parameters.sourcePartition index)
        Reference
        ((namedMeasuredMiddleInstrument parameters index environment).operator original
          (pointOutcome, outcome))
        (point.2.2.record original pointOutcome).1.1 outcome column target scalar := by
  dsimp only
  intro pointOutcome outcome column target scalar pointAction
  exact measuredMiddleFeedKetAction_of_eq (parameters.ports index)
    (parameters.sourcePartition index) Reference _ _ _ outcome column target scalar
    (namedMeasuredMiddle_operator parameters index environment original (pointOutcome, outcome))
    pointAction

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
