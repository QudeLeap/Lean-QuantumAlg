/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Core.Execution.Instrument.Support

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Chain

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction

/-!
# Actual allocating point execution preserves reference support on every input label
The builder's real service-state updates and the lexical workspace records
are retained. Reference support is propagated from the actual Chain Kraus
equation, independently of the separate reference-unitary naturality law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

open ClassicalRoutines.EllipticCurve.WindowTables

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth window : Nat}

/-- Actual table-builder records retain reference support, including overwritten cells. -/
lemma table_referenceSupported (frame : TableFrame ctx wordWidth (2 ^ window))
    (spec : ModulusSpec wordWidth)
      (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.ReferenceSupported
      (frame.circuit (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec)
      environment := by
  intro Reference allowed History _ state supported result basis absent
  rw [frame.tableCircuit_execute spec environment]
  exact Execution.classical_reference_support state _ allowed supported result basis absent

/-- The real allocating five-array scope preserves reference support of its actual strict body. -/
lemma constructedTables_referenceSupported (frame : Outer.Frame ctx wordWidth)
    (spec : ModulusSpec wordWidth) (row : Fin 34)
    (body : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      TableFrame inner wordWidth (2 ^ window) →
        Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
        inner inner false)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (actual : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (table : TableFrame inner wordWidth (2 ^ window)),
      Execution.ReferenceSupported (body lift same table) environment) :
    Execution.ReferenceSupported (frame.withConstructedQuantumTables spec row body) environment :=
      by
  unfold Outer.Frame.withConstructedQuantumTables withCellsWithQuantumWires
  refine withCellsWithQuantumWiresFrom_property (Transport.id ctx) rfl _ _
    (fun {inner} _ _ code => Execution.ReferenceSupported code environment) ?_ ?_
  · intro inner lift same key shape fresh code supported
    exact Execution.ReferenceSupported.workspace environment key shape fresh code supported
  · intro inner cells distinct lift separated same
    let table := frame.tableFrame lift cells distinct separated row
    exact (table_referenceSupported table spec environment).seq
      ((actual lift (quantumLayout_wires_of_quantumWires same) table).embed_identity)

/-- The actual complete paid point Driver cannot create an absent external-reference coordinate. -/
lemma driver_reference_supported (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.ReferenceSupported (Driver.circuit parameters frame spec row) environment :=
  constructedTables_referenceSupported frame spec row
    (fun lift same table => (Driver.kernelParameters parameters lift same table.arrays).circuit)
    environment (fun lift same table =>
      (chain_hasInstrument (Driver.kernelParameters parameters lift same table.arrays)
        environment).reference_supported)

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
