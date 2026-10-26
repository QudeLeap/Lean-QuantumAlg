/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Naturality
import all QuantumAlg.Core.Execution.Instrument.Support
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Middle
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Trace
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Native

/-!
# All-input reference laws of the original measured sampling list

The proof follows the unchanged reset/H/paid measured point/Fourier syntax.
Its list induction never unfolds a point body or native gate list. Complete
Store, service state and real measurement Paths survive, including on bad
arithmetic labels. These are locality laws, not point-correctness or Born
assertions; no mathematical source is allocated by the actual program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution Locality
open QuantumFourierTransform.Semiclassical.Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma native_referenceTraceNatural
    (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    ReferenceTraceNatural (Circuit.unitary (operations := BitWord.model)
      (classicalOracles := services) (allowAllocation := true) program) environment := by
  intro Reference Frame History _ state
  exact Circuit.execute_forgetReferenceFrame
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := services)
      (allowAllocation := false) program) environment state

namespace Parameters

/-- The real reset/H/measured-middle block commutes with arbitrary reference unitaries. -/
lemma sampling_block_referenceNatural (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (parameters.block index) environment :=
  (parameters.sampling_reset_referenceNatural index environment).seq
    (Execution.ReferenceNatural.seq
      ((nativeInstrument (operations := BitWord.model) (services := services)
      (allowAllocation := true) (preparation (index.lowerWidth + 1)
        (parameters.ports index)) environment).to_exists.reference_unitary)
      (parameters.sampling_measuredMiddle_referenceNatural index environment))

/-- Every actual block preserves support of its full arbitrary reference, on all labels. -/
lemma sampling_block_referenceSupported (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceSupported (parameters.block index) environment :=
  (parameters.sampling_reset_referenceSupported index environment).seq
    (((nativeInstrument (operations := BitWord.model) (services := services)
      (allowAllocation := true) (preparation (index.lowerWidth + 1)
        (parameters.ports index)) environment).to_exists.reference_supported).seq
      (parameters.sampling_measuredMiddle_referenceSupported index environment))

/-- Actual block execution commutes with discarding any mathematical reference factor. -/
lemma sampling_block_referenceTraceNatural (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : ReferenceTraceNatural (parameters.block index) environment :=
  (ReferenceTraceNatural.embed_identity
    (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index))
    environment).seq
    ((native_referenceTraceNatural
      (preparation (index.lowerWidth + 1) (parameters.ports index)) environment).seq
      ((driver_reference_partialTrace (parameters.pointParameters index) parameters.frame
        parameters.modulus index.row environment).seq
        (ReferenceTraceNatural.embed_identity (inverseCode (parameters.ports index)) environment)))

/-- Structural composition retains unitary naturality of the same original window list. -/
lemma sampling_sequence_referenceNatural (parameters : Parameters ctx) (indices : List WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (parameters.sequence indices)
        environment := by
  induction indices with
  | nil =>
      change Execution.ReferenceNatural (Circuit.id
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (allowAllocation := true) ctx) environment
      intro Reference operator History _ state
      rw [Circuit.execute_id, Circuit.execute_id]
      exact classical_unitary state _ _
  | cons index rest ih =>
      exact (parameters.sampling_block_referenceNatural index environment).seq ih

/-- Every real complete list record preserves each internally established reference support. -/
lemma sampling_sequence_referenceSupported (parameters : Parameters ctx)
    (indices : List WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceSupported (parameters.sequence indices)
        environment := by
  induction indices with
  | nil =>
      change Execution.ReferenceSupported (Circuit.id
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (allowAllocation := true) ctx) environment
      intro Reference allowed History _ state supported result basis absent
      rw [Circuit.execute_id]
      exact classical_reference_support state _ allowed supported result basis absent
  | cons index rest ih =>
      exact (parameters.sampling_block_referenceSupported index environment).seq ih

/-- The same real list permits exact removal of an arbitrary mathematical reference factor. -/
lemma sampling_sequence_referenceTraceNatural (parameters : Parameters ctx)
    (indices : List WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : ReferenceTraceNatural (parameters.sequence indices) environment := by
  induction indices with
  | nil =>
      intro Reference Frame History _ state
      exact Circuit.execute_forgetReferenceFrame
        (Circuit.id (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          (allowAllocation := false) ctx) environment state
  | cons index rest ih =>
      exact (parameters.sampling_block_referenceTraceNatural index environment).seq ih

end Parameters

/-- The literal actual34 sampler has all-input reference-unitary naturality. -/
lemma sampling_circuit_referenceNatural (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (circuit parameters) environment :=
  parameters.sampling_sequence_referenceNatural schedule environment

/-- The literal actual34 sampler preserves every absent reference coordinate. -/
lemma sampling_circuit_referenceSupported (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceSupported (circuit parameters) environment :=
  parameters.sampling_sequence_referenceSupported schedule environment

/-- The literal actual34 sampler commutes with discarding a mathematical reference factor. -/
lemma sampling_circuit_referenceTraceNatural (parameters : Parameters ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : ReferenceTraceNatural (circuit parameters) environment :=
  parameters.sampling_sequence_referenceTraceNatural schedule environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
