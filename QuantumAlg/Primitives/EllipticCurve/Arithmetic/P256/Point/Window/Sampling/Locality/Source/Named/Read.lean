/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source.Named
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Correctness.Read.Inputs
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Store

/-!
# Original inputs after the actual point and Fourier window

The real point record retains the original modulus, constants and all
base-array rows. The following Fourier feedback and measured readout write
only their actual finite-two output cells. Thus the next window receives
the same original input readings in every complete actual record, without
any arithmetic value, point-action or sampling-success assumption.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def NamedMiddlePreservesRead (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {shape : CShape} (observed : CStorageRef ctx shape) : Prop :=
  let point := namedDriverInstrument (services := services) (parameters.pointParameters index)
    parameters.frame parameters.modulus index.row environment
  letI : Fintype point.1 := point.2.1
  ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
    ((namedMeasuredMiddleInstrument parameters index environment).record
      original outcomes).1.1.read (.storage observed) = original.1.read (.storage observed)

attribute [local irreducible] NamedMiddlePreservesRead NamedDriverPreservesRead frameInputKeys

private lemma namedMeasuredMiddle_read_of_point (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {shape : CShape} (observed : CStorageRef ctx shape)
    (pointRead : NamedDriverPreservesRead (parameters.pointParameters index) parameters.frame
      parameters.modulus index.row environment observed)
    (fourierFree : ∀ bit, ((parameters.ports index).output bit).key ≠ observed.key) :
    NamedMiddlePreservesRead parameters index environment observed := by
  unfold NamedMiddlePreservesRead
  dsimp only
  intro original outcomes
  rw [namedMeasuredMiddle_record]
  dsimp only
  rw [inverseStoreRecord_store]
  unfold NamedDriverPreservesRead at pointRead
  exact (window_outcomeStore_read_untouched _ _ _ _ observed fourierFree).trans
    (pointRead original outcomes.1)

/-- The original loaded words survive the actual point execution and its Fourier readout. -/
lemma namedMeasuredMiddle_frame_word_read (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width : Nat} (observed : CStorageRef ctx (.unsignedWord width))
    (originalInput : observed.key ∈ frameInputKeys parameters.frame) :
    NamedMiddlePreservesRead parameters index environment observed := by
  apply namedMeasuredMiddle_read_of_point
  · exact namedDriverInstrument_frame_word_read (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment observed originalInput
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)

/-- All original base rows survive together in their actual arrays after the same full window. -/
lemma namedMeasuredMiddle_array_read (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width length : Nat} (observed : CStorageRef ctx (.fixedVector length (.unsignedWord width))) :
    NamedMiddlePreservesRead parameters index environment observed := by
  apply namedMeasuredMiddle_read_of_point
  · exact namedDriverInstrument_array_read (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment observed
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
