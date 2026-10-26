/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Instrument
import all QuantumAlg.Core.Execution.Instrument.Allocation.Read
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record.Read
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store.Phases
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program

/-!
# Original Fourier reads in the specified actual Driver certificate

The paid builder preserves the finite-two cells by their actual storage
shapes. The measured point preserves them by the original caller's explicit
separation from its feedback destinations. Each real workspace pushes and
pops the same read. The certificate retains the complete actual Store,
returned service state and both chronological Paths.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open QuantumAlg.Execution.Instrument

open Sampling

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma tablePrefixInstrument_read_finite {width window : Nat}
    (table : TableFrame ctx width (2 ^ window)) (spec : ModulusSpec width)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true}
    {Outcome : Type} [Fintype Outcome] (actual : Instrument body Outcome environment)
    (observed : CStorageRef ctx (.finite 2))
    (bodyRead : ∀ store outcome, (actual.record store outcome).1.read (.storage observed) =
      store.read (.storage observed)) (original : Store ctx × services.HiddenState)
    (outcome : Outcome) :
    ((tablePrefixInstrument table spec environment actual).record original outcome).1.1.read
        (.storage observed) = original.1.read (.storage observed) := by
  change (actual.record (table.circuitRecord
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    spec environment original).1.1 outcome).1.read (.storage observed) = _
  exact (bodyRead _ outcome).trans (table.circuitRecord_read_finite
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    spec environment observed original)

private lemma transported_read_free {inner : RuntimeCtx .quantum}
    (lift : Transport ctx inner) {shape : CShape} (output : CWriteRef ctx shape)
    (observed : CStorageRef ctx (.finite 2)) (free : output.key ≠ observed.key) :
    (lift.liftWrite output).key ∉ (CInputRef.storage (lift.liftStorage observed)).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton,
    Transport.liftWrite_key, Transport.liftStorage_key] using free

/-- The specified actual Driver retains an original finite-two read in every real record. -/
lemma namedDriverInstrument_read_finite (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (observed : CStorageRef ctx (.finite 2))
    (outputFree : ∀ bit, (parameters.output bit).key ≠ observed.key)
    (maskFree : parameters.mask.key ≠ observed.key)
    (parityFree : ∀ bit, (parameters.parity bit).key ≠ observed.key)
    (temporaryFree : parameters.temporary.key ≠ observed.key) :
    let chosen := namedDriverInstrument parameters frame spec row environment
    letI : Fintype chosen.1 := chosen.2.1
    ∀ original outcome, (chosen.2.2.record original outcome).1.1.read (.storage observed) =
      original.1.read (.storage observed) := by
  exact recordedWithCells_read (ctx := ctx) (operations := BitWord.model)
    (services := services) (environment := environment)
    (Outer.tableShapes 256 (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)))
    (fun {inner} cells distinct lift separated same =>
      ((frame.tableFrame lift cells distinct separated row).circuit
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec).seq
        (Circuit.embed (allowAllocation := true)
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          (ContextEmbedding.identity inner)
          (Driver.kernelParameters parameters lift (quantumLayout_wires_of_quantumWires same)
            (frame.tableFrame lift cells distinct separated row).arrays).circuit))
    (fun {inner} cells distinct lift separated same =>
      (tablePrefixInstrument (ctx := inner) (services := services)
        (frame.tableFrame lift cells distinct separated row) spec environment
        ((Driver.kernelParameters parameters lift (quantumLayout_wires_of_quantumWires same)
          (frame.tableFrame lift cells distinct separated row).arrays).pointProgramInstrument
            environment).embedIdentity).pack)
    (.storage observed) (by
      intro inner cells distinct lift separated same
      let chosen := (tablePrefixInstrument (ctx := inner) (services := services)
        (frame.tableFrame lift cells distinct separated row) spec environment
        ((Driver.kernelParameters parameters lift (quantumLayout_wires_of_quantumWires same)
          (frame.tableFrame lift cells distinct separated row).arrays).pointProgramInstrument
            environment).embedIdentity).pack
      let _ : Fintype chosen.1 := chosen.2.1
      apply tablePrefixInstrument_read_finite (ctx := inner) (services := services)
      exact (Driver.kernelParameters parameters lift
        (quantumLayout_wires_of_quantumWires same)
        (frame.tableFrame lift cells distinct separated row).arrays).pointProgramInstrument_read
          environment (.storage (lift.liftStorage observed))
          (fun bit => transported_read_free lift _ observed (outputFree bit))
          (transported_read_free lift _ observed maskFree)
          (fun bit => transported_read_free lift _ observed (parityFree bit))
          (transported_read_free lift _ observed temporaryFree))

/-- The original sampler's separation supplies all read conditions for its own Fourier cells. -/
lemma namedDriverInstrument_result_read (parameters : Sampling.Parameters ctx) (index : WindowIndex)
    (position : QuantumFourierTransform.Semiclassical.Window.BitPosition 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    let chosen := namedDriverInstrument (parameters.pointParameters index) parameters.frame
      parameters.modulus index.row environment
    letI : Fintype chosen.1 := chosen.2.1
    ∀ original outcome,
      (chosen.2.2.record original outcome).1.1.read
          (.storage (parameters.results.cells position).toCStorageRef) =
        original.1.read (.storage (parameters.results.cells position).toCStorageRef) := by
  apply namedDriverInstrument_read_finite
  · exact fun bit => parameters.output_separate bit position
  · exact parameters.mask_separate position
  · exact fun bit => parameters.parity_separate (Fin.castLE index.lowCapacity bit) position
  · exact parameters.temporary_separate position

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
