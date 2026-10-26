/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Append
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Fourier.Scalars
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Scalars

/-!
# Literal retained prefix updates of the actual named window

Every point outcome retains the same prior Fourier cells. The same named
middle appends its real Fourier outcome and retains the other complete stream.
These equalities refer to the original Store returned by its actual record.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] Driver.namedDriverInstrument Locality.namedMeasuredMiddleInstrument

/-- Every original stream prefix survives the actual all-zero reset record. -/
lemma reset_zero_retainedPrefix (parameters : Parameters ctx) (index : WindowIndex)
    (stream : Fin 2) (count : Nat) (bounded : count ≤ 260) (before : Store ctx) :
    Feedback.retainedPrefix parameters.results.cells stream count bounded
        (parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) before).1 =
      Feedback.retainedPrefix parameters.results.cells stream count bounded before := by
  apply Feedback.retainedPrefix_congr
  intro position
  exact reset_zero_result_read parameters index before (stream, Fin.castLE bounded position)

namespace Parameters

variable (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

/-- Every actual named record appends exactly its own measured outcome to its real prefix. -/
lemma named_middle_retainedPrefix :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      Feedback.retainedPrefix parameters.results.cells index.stream
          (index.lowerWidth + 1 + index.start) (by have := index.within; omega)
          ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
            original outcomes).1.1 =
        Partner.blockBits index.start (index.lowerWidth + 1)
          (Feedback.storedPrefix (parameters.ports index) original.1) outcomes.2 := by
  dsimp only
  intro original outcomes
  exact Feedback.retainedPrefix_append (parameters.ports index) original.1 _ outcomes.2
    (fun previous prior => parameters.named_middle_past_read index environment
      previous prior original outcomes)
    (fun bit => parameters.named_middle_current_bit index environment bit original outcomes)

/-- Cells of the other original stream are untouched by every real named-middle outcome. -/
lemma named_middle_other_read (previous : BitPosition 260)
    (other : previous.1 ≠ index.stream) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
        original outcomes).1.1.read
          (.storage (parameters.results.cells previous).toCStorageRef) =
        original.1.read (.storage (parameters.results.cells previous).toCStorageRef) := by
  dsimp only
  intro original outcomes
  rw [Locality.namedMeasuredMiddle_record]
  dsimp only
  rw [inverseStoreRecord_store]
  refine (window_outcomeStore_read_untouched _ (parameters.ports index) _ outcomes.2
    (parameters.results.cells previous).toCStorageRef ?_).trans
      (Driver.namedDriverInstrument_result_read parameters index previous environment
        original outcomes.1)
  intro bit same
  have positions := parameters.results.distinct same
  exact other (congrArg Prod.fst positions).symm

/-- The complete other stream remains the same physical record, including after the last window. -/
lemma named_middle_other_prefix (stream : Fin 2) (other : stream ≠ index.stream)
    (count : Nat) (bounded : count ≤ 260) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      Feedback.retainedPrefix parameters.results.cells stream count bounded
          ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
            original outcomes).1.1 =
        Feedback.retainedPrefix parameters.results.cells stream count bounded original.1 := by
  dsimp only
  intro original outcomes
  apply tupleCoordinates_injective count
  funext position
  rw [Feedback.retainedPrefix_coordinate, Feedback.retainedPrefix_coordinate]
  exact congrArg CShape.Value.toFin
    (parameters.named_middle_other_read index environment
      (stream, Fin.castLE bounded position) other original outcomes)

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
