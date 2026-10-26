/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Core.Execution.Instrument.Allocation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Phases
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record

/-!
# The specified point instrument in the actual five-array Driver scope

The named chronological point instrument follows the real paid builder.
Its operator reads the builder's actual returned Store, while its complete
record retains the actual returned hidden state and both original Paths.
The original allocator wraps this specified certificate directly. No
instrument is selected from an existence proposition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open QuantumAlg.Execution.Instrument

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

open Sampling

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Compose the specified body after a symbolic-width actual table record. -/
private def tablePrefixInstrument {width window : Nat}
    (table : TableFrame ctx width (2 ^ window)) (spec : ModulusSpec width)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true}
    {Outcome : Type} [Fintype Outcome]
    (actual : Instrument body Outcome environment) :
    RecordedInstrument ((table.circuit
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec).seq body)
      Outcome environment :=
  Instrument.recordedPrefix (ctx := ctx) (operations := BitWord.model) (services := services)
    (environment := environment) (body := body) (Outcome := Outcome)
    (preparation := table.circuit
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec)
    (table.circuitRecord
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec environment)
    (fun Reference {History} _ state => table.tableCircuit_execute (History := History)
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      spec environment Reference state)
    actual

/-- The exact named point certificate passes through its actual builder and lexical scopes. -/
def namedDriverInstrument (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    RecordedInstrument.Packed (ctx := ctx) (operations := BitWord.model) (services := services)
      (Driver.circuit (services := services) parameters frame spec row) environment := by
  unfold Driver.circuit Outer.Frame.withConstructedQuantumTables
  apply recordedWithCells
  intro inner cells distinct lift separated same
  let table := frame.tableFrame lift cells distinct separated row
  let kernel := Driver.kernelParameters parameters lift
    (quantumLayout_wires_of_quantumWires same) table.arrays
  let point := kernel.pointProgramInstrument environment
  let embedded := point.embedIdentity
  let combined := tablePrefixInstrument table spec environment embedded
  exact combined.pack

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
