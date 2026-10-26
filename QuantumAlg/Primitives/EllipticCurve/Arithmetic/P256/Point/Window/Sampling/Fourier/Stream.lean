/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Fourier.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Address
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Blocks
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Scalars
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases

/-!
# Exact original stream rows through the real retained records

The existing two-block Fourier identity telescopes each actual window's
scalar into the row of its newly retained prefix. The input uses the original
unsigned source bits. At the terminal cursor the output frequency is exactly
the bit reversal read by the existing paid decoder.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The exact Fourier row of the currently retained original stream prefix. -/
def streamFourierRow (parameters : Parameters ctx) (stream : Fin 2)
    (count : Nat) (bounded : count ≤ 260) (store : Store ctx) (source : Fin (2 ^ 260)) : ℂ :=
  Partner.fourierRows true count
    (Feedback.retainedPrefix parameters.results.cells stream count bounded store)
    (Partner.prefixBits count bounded ((binaryEquiv 260).symm source))

private lemma prefix_row_append (head tail : Nat) (frontOutput frontInput : Bits head)
    (output input : Bits tail) (α : ℂ) :
    Partner.fourierRows true head frontOutput frontInput *
        (α * (Partner.fourierRows true tail output input *
          Partner.phaseBasis tail
            (Partner.suffixPhases true head tail (fun _ => 1) frontOutput) input)) =
      α * Partner.fourierRows true (tail + head)
        (Partner.blockBits head tail frontOutput output)
        (Partner.blockBits head tail frontInput input) := by
  have cut := Partner.qftPartner_fourierRows_phaseBasis_blocks true head tail
    (fun _ => 1) frontOutput frontInput output input
  have prefixUnit : Partner.phaseBasis head
      (Partner.prefixFamily tail head (fun _ => 1)) frontInput = 1 :=
    Partner.phaseBasis_one head frontInput
  rw [Partner.phaseBasis_one, mul_one, prefixUnit, mul_one] at cut
  rw [cut]
  ring

/-- The actual selected digit has its unchanged original MSB-first source coordinates. -/
lemma sourcePartition_stream_coordinate (parameters : Parameters ctx) (index : WindowIndex)
    (source : SourceRegister.Index) (bit : Fin (index.lowerWidth + 1)) :
    tupleCoordinates (index.lowerWidth + 1)
        ((binaryEquiv (index.lowerWidth + 1)).symm
          (parameters.sourcePartition index source).1) bit =
      tupleCoordinates 260 ((binaryEquiv 260).symm (sourceValue index source))
        ((parameters.ports index).position bit) := by
  simp only [tupleCoordinates, Equiv.apply_symm_apply]
  conv_rhs => rw [BinaryBasis.bigEndianEquiv_symm_value]
  exact window_sourcePartition_stream (parameters.ports index) source.1 source.2 bit

/-- The selected actual source digit appends to the same original unsigned input prefix. -/
lemma sourcePartition_prefix_append (parameters : Parameters ctx) (index : WindowIndex)
    (source : SourceRegister.Index) :
    Partner.prefixBits (index.lowerWidth + 1 + index.start)
        (by have := index.within; omega) ((binaryEquiv 260).symm (sourceValue index source)) =
      Partner.blockBits index.start (index.lowerWidth + 1)
        (Partner.prefixBits index.start (by have := index.within; omega)
          ((binaryEquiv 260).symm (sourceValue index source)))
        ((binaryEquiv (index.lowerWidth + 1)).symm
          (parameters.sourcePartition index source).1) := by
  apply Partner.prefixBits_append
  intro bit
  exact sourcePartition_stream_coordinate parameters index source bit

attribute [local irreducible] Driver.namedDriverInstrument Locality.namedMeasuredMiddleInstrument

/-- One actual window advances its original stream's exact coherent Fourier row. -/
lemma named_middle_stream_row (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (source : SourceRegister.Index) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      streamFourierRow parameters index.stream index.start (by have := index.within; omega)
          original.1 (sourceValue index source) *
          windowScalar parameters index original.1 source outcomes.2 =
        (NormalizedVector.invSqrt2 ^ 2048) *
          streamFourierRow parameters index.stream (index.lowerWidth + 1 + index.start)
            (by have := index.within; omega)
            ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
              original outcomes).1.1 (sourceValue index source) := by
  dsimp only
  intro original outcomes
  unfold streamFourierRow
  rw [parameters.named_middle_retainedPrefix index environment original outcomes,
    sourcePartition_prefix_append parameters index source,
    windowScalar_fourierRows]
  have prefixEq : Feedback.retainedPrefix parameters.results.cells index.stream index.start
      (by have := index.within; omega) original.1 =
        Feedback.storedPrefix (parameters.ports index) original.1 :=
    Feedback.retainedPrefix_before (parameters.ports index) original.1
  rw [prefixEq]
  exact prefix_row_append index.start (index.lowerWidth + 1)
    (Feedback.storedPrefix (parameters.ports index) original.1) _ outcomes.2 _ _

/-- The same actual record leaves every row of the other original stream unchanged. -/
lemma named_middle_other_row (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (stream : Fin 2) (other : stream ≠ index.stream)
    (count : Nat) (bounded : count ≤ 260) (source : Fin (2 ^ 260)) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)),
      streamFourierRow parameters stream count bounded
          ((Locality.namedMeasuredMiddleInstrument parameters index environment).record
            original outcomes).1.1 source =
        streamFourierRow parameters stream count bounded original.1 source := by
  dsimp only
  intro original outcomes
  unfold streamFourierRow
  rw [parameters.named_middle_other_prefix index environment stream other count bounded]

/-- The literal zero reset changes no row of either original retained prefix. -/
lemma reset_zero_streamFourierRow (parameters : Parameters ctx) (index : WindowIndex)
    (stream : Fin 2) (count : Nat) (bounded : count ≤ 260)
    (store : Store ctx) (source : Fin (2 ^ 260)) :
    streamFourierRow parameters stream count bounded
        (parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) store).1 source =
      streamFourierRow parameters stream count bounded store source := by
  unfold streamFourierRow
  rw [reset_zero_retainedPrefix]

private lemma empty_fourierRow (inverse : Bool) (output input : Bits 0) :
    Partner.fourierRows inverse 0 output input = 1 := by
  cases output
  cases input
  rfl

/-- The initial empty stream prefix contributes exactly the unit Fourier scalar. -/
lemma streamFourierRow_initial (parameters : Parameters ctx) (stream : Fin 2)
    (store : Store ctx) (source : Fin (2 ^ 260)) :
    streamFourierRow parameters stream 0 (Nat.zero_le 260) store source = 1 := by
  exact empty_fourierRow true _ _

/-- The terminal row has exactly the original decoder's reversed frequency label. -/
lemma streamFourierRow_terminal (parameters : Parameters ctx) (stream : Fin 2)
    (store : Store ctx) (source : Fin (2 ^ 260)) :
    streamFourierRow parameters stream 260 (Nat.le_refl 260) store source =
      Partner.fullRows true 260
        (Decode.storedFrequency parameters.results.cells stream store)
        ((binaryEquiv 260).symm source) := by
  exact Feedback.retainedPrefix_fullRows true parameters.results.cells stream store
    ((binaryEquiv 260).symm source)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
