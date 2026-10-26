/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.GateModel.Algorithm
import all
QuantumAlg.Core.Execution.Instrument.Naturality

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Scope.Quantum
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction

/-!
# Actual paid five-array construction preserves the external reference
The original classical table builder keeps its complete real record. The
actual lexical allocator then lifts the body's proved reference law through
each original workspace. Table dimensions remain symbolic throughout.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

open ClassicalRoutines.EllipticCurve.WindowTables

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth window : Nat}

/-- The same paid table program changes only its actual classical records, for any input Store. -/
lemma table_referenceNatural (frame : TableFrame ctx wordWidth (2 ^ window))
    (spec : ModulusSpec wordWidth)
      (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.ReferenceNatural
      (frame.circuit (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec)
      environment := by
  intro Reference operator History _ state
  rw [frame.tableCircuit_execute spec environment, frame.tableCircuit_execute spec environment]
  exact classical_unitary _ _ _

/-- The actual allocating table scope retains its real body's arbitrary-reference law. -/
lemma constructedTables_referenceNatural (frame : Outer.Frame ctx wordWidth)
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
      Execution.ReferenceNatural (body lift same table) environment) :
    Execution.ReferenceNatural (frame.withConstructedQuantumTables spec row body) environment := by
  unfold Outer.Frame.withConstructedQuantumTables withCellsWithQuantumWires
  refine withCellsWithQuantumWiresFrom_property (Transport.id ctx) rfl _ _
    (fun {inner} _ _ code => Execution.ReferenceNatural code environment) ?_ ?_
  · intro inner lift same key shape fresh code natural
    exact Execution.ReferenceNatural.workspace environment key shape fresh code natural
  · intro inner cells distinct lift separated same
    let table := frame.tableFrame lift cells distinct separated row
    exact (table_referenceNatural table spec environment).seq
      ((actual lift (quantumLayout_wires_of_quantumWires same) table).embed_identity)

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
