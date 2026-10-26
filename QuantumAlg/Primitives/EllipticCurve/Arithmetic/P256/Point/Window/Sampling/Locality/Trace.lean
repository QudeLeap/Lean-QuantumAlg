/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Workspace
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction
import all QuantumAlg.Core.Execution.Composition.Identity

/-!
# Actual allocating Driver execution and reference partial trace

The strict actual point body uses the existing full Circuit law. The paid
table builder retains its genuine Store and service-state writes, and every
lexical workspace uses its real push/body/pop. Thus the original allocating
Driver commutes with discarding an arbitrary reference factor, on all labels
and complete actual records. No arithmetic admission is needed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.WindowTables
open QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- Discarding a reference factor preserves the actual interpreter's complete real records. -/
def ReferenceTraceNatural (code : Circuit (.quantum gates oracles operations services)
    ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment) : Prop :=
  ∀ (Reference Frame : Register) {History : Type} [Fintype History]
    (state : State ctx (Frame.prod Reference) (services.HiddenState × History)),
    code.execute environment Reference state.forgetReferenceFrame =
      (code.execute environment (Frame.prod Reference) state).forgetReferenceFrame

/-- Actual sequential execution retains reference partial trace and both chronological paths. -/
lemma ReferenceTraceNatural.seq
    {first second : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations services).Environment}
    (head : ReferenceTraceNatural first environment)
    (tail : ReferenceTraceNatural second environment) :
    ReferenceTraceNatural (first.seq second) environment :=
  window_source_sequence_partialTrace environment first second head tail

/-- The literal identity embedding keeps the strict child's existing full reference-trace law. -/
lemma ReferenceTraceNatural.embed_identity
    (code : Circuit (.quantum gates oracles operations services) ctx ctx false)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment) :
    ReferenceTraceNatural
      (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity _) code) environment := by
  intro Reference Frame History _ state
  exact (Circuit.execute_identity_embed (allowAllocation := true)
    code environment Reference state.forgetReferenceFrame).trans
      ((Circuit.execute_forgetReferenceFrame code environment state).trans
        (congrArg (fun current : State ctx (Frame.prod Reference)
            (services.HiddenState × (History × code.Path)) => current.forgetReferenceFrame)
          (Circuit.execute_identity_embed (allowAllocation := true)
            code environment (Frame.prod Reference) state).symm))

/-- The actual classical workspace retains its real child's partial-trace equation. -/
lemma ReferenceTraceNatural.workspace
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true)
    (actual : ReferenceTraceNatural body environment) :
    ReferenceTraceNatural (Circuit.workspace
      (model := .quantum gates oracles operations services) ctx key shape fresh body)
      environment :=
  window_source_workspace_partialTrace environment key shape fresh body actual

/-- The real table builder keeps its actual full classical records under reference projection. -/
lemma table_referenceTraceNatural {wordWidth window : Nat}
    (frame : TableFrame ctx wordWidth (2 ^ window)) (spec : ModulusSpec wordWidth)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    ReferenceTraceNatural
      (frame.circuit (model := .quantum AlgorithmGate.model .empty BitWord.model services) spec)
      environment := by
  intro Reference Frame History _ state
  rw [frame.tableCircuit_execute spec environment, frame.tableCircuit_execute spec environment]
  exact classical_trace state _

/-- The actual five-array allocator retains every caller block and real strict-body path. -/
lemma constructedTables_referenceTraceNatural {wordWidth window : Nat}
    (frame : Outer.Frame ctx wordWidth) (spec : ModulusSpec wordWidth) (row : Fin 34)
    (body : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      TableFrame inner wordWidth (2 ^ window) →
        Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner false)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    ReferenceTraceNatural (frame.withConstructedQuantumTables spec row body) environment := by
  unfold Outer.Frame.withConstructedQuantumTables withCellsWithQuantumWires
  refine withCellsWithQuantumWiresFrom_property (Transport.id ctx) rfl _ _
    (fun {inner} _ _ code => ReferenceTraceNatural code environment) ?_ ?_
  · intro inner lift same key shape fresh code actual
    exact ReferenceTraceNatural.workspace environment key shape fresh code actual
  · intro inner cells distinct lift separated same
    let table := frame.tableFrame lift cells distinct separated row
    exact (table_referenceTraceNatural table spec environment).seq
      (ReferenceTraceNatural.embed_identity
        (body lift (quantumLayout_wires_of_quantumWires same) table) environment)

/-- The literal actual Driver permits removal of a mathematical source without dropping records. -/
lemma driver_reference_partialTrace (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    ReferenceTraceNatural (Driver.circuit parameters frame spec row) environment :=
  constructedTables_referenceTraceNatural frame spec row
    (fun lift same table => (Driver.kernelParameters parameters lift same table.arrays).circuit)
    environment

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
