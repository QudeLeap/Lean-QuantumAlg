/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Instrument
import all QuantumAlg.Core.Execution.Instrument.Allocation.Read
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Record.Read.Other
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Store.Phases
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program

/-!
# Structural caller reads through the actual constructed-table Driver

The actual five arrays are fresh for every original caller read. Only the
four persistent working words and the measured kernel's feedback cells
need explicit separation. Both real chronological records and all actual
workspace scopes preserve any read satisfying these placement conditions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open QuantumAlg.Execution.Instrument

open Sampling

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma tablePrefixInstrument_read_separate {width window : Nat}
    (table : TableFrame ctx width (2 ^ window)) (spec : ModulusSpec width)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true}
    {Outcome : Type} [Fintype Outcome] (actual : Instrument body Outcome environment)
    {shape : CShape} (observed : CStorageRef ctx shape)
    (tableFree : ∀ key ∈ table.outputKeys,
      key ∉ (CInputRef.storage observed).storageKeys)
    (bodyRead : ∀ store outcome, (actual.record store outcome).1.read (.storage observed) =
      store.read (.storage observed)) (original : Store ctx × services.HiddenState)
    (outcome : Outcome) :
    ((tablePrefixInstrument table spec environment actual).record original outcome).1.1.read
        (.storage observed) = original.1.read (.storage observed) := by
  change (actual.record (table.circuitRecord
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    spec environment original).1.1 outcome).1.read (.storage observed) = _
  exact (bodyRead _ outcome).trans (table.circuitRecord_read_other
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    spec environment (.storage observed) tableFree original)

private lemma transported_read_free {inner : RuntimeCtx .quantum}
    (lift : Transport ctx inner) {outputShape : CShape} (output : CWriteRef ctx outputShape)
    {shape : CShape} (observed : CStorageRef ctx shape) (free : output.key ≠ observed.key) :
    (lift.liftWrite output).key ∉ (CInputRef.storage (lift.liftStorage observed)).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton,
    Transport.liftWrite_key, Transport.liftStorage_key] using free

private def frameWorkKeys {kind : ProblemKind} {c : RuntimeCtx kind} {width : Nat}
    (frame : Outer.Frame c width) : List StorageKey :=
  [frame.product.key, frame.inverse.key, frame.temporary.key, frame.slope.key]

private def frameInputKeys {kind : ProblemKind} {c : RuntimeCtx kind} {width : Nat}
    (frame : Outer.Frame c width) : List StorageKey :=
  [frame.modulus.key, frame.zero.key, frame.one.key, frame.curveA.key]

private def frameBaseKeys {kind : ProblemKind} {c : RuntimeCtx kind} {width : Nat}
    (frame : Outer.Frame c width) : List StorageKey := [frame.x.key, frame.y.key]

attribute [local irreducible] frameWorkKeys frameInputKeys frameBaseKeys

private lemma frame_work_input_disjoint {kind : ProblemKind} {c : RuntimeCtx kind} {width : Nat}
    (frame : Outer.Frame c width) : List.Disjoint (frameWorkKeys frame) (frameInputKeys frame) := by
  have distinct : (frameWorkKeys frame ++ (frameInputKeys frame ++ frameBaseKeys frame)).Nodup := by
    simpa only [frameWorkKeys, frameInputKeys, frameBaseKeys,
      List.cons_append, List.nil_append] using frame.distinct
  have separate := List.disjoint_of_nodup_append distinct
  exact List.disjoint_left.mpr fun _ written original =>
    List.disjoint_left.mp separate written (List.mem_append_left _ original)

private lemma constructed_table_outputKeys {width length : Nat}
    (frame : Outer.Frame ctx width) {inner : RuntimeCtx .quantum}
    (lift : Transport ctx inner) (cells : Cells inner (Outer.tableShapes width length))
    (distinct : cells.Distinct) (separated : cells.TransportSeparated lift) (row : Fin 34) :
    (frame.tableFrame lift cells distinct separated row).outputKeys =
      cells.keys ++ frameWorkKeys frame := by
  rw [← Outer.arraysOfCells_keys cells distinct]
  simp only [TableFrame.outputKeys, Outer.Frame.tableFrame, Outer.Frame.transport,
    Outer.Frame.work, Transport.liftWrite_key, frameWorkKeys, List.cons_append, List.nil_append]

private lemma constructed_table_read_free {width length : Nat}
    (frame : Outer.Frame ctx width) {inner : RuntimeCtx .quantum}
    (lift : Transport ctx inner) (cells : Cells inner (Outer.tableShapes width length))
    (distinct : cells.Distinct) (separated : cells.TransportSeparated lift) (row : Fin 34)
    {shape : CShape} (observed : CStorageRef ctx shape)
    (workFree : ∀ key ∈ frameWorkKeys frame, key ≠ observed.key) :
    ∀ key ∈ (frame.tableFrame lift cells distinct separated row).outputKeys,
      key ∉ (CInputRef.storage (lift.liftStorage observed)).storageKeys := by
  intro key written
  have writes : key ∈ cells.keys ++ frameWorkKeys frame := by
    rwa [constructed_table_outputKeys] at written
  rcases List.mem_append.mp writes with fresh | persistent
  · exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells lift separated
      fresh (.storage observed)
  · simpa only [CInputRef.storageKeys, List.mem_singleton, Transport.liftStorage_key]
      using workFree key persistent

private lemma frame_work_read_free {width : Nat} (frame : Outer.Frame ctx width)
    (observed : StorageKey) (originalInput : observed ∈ frameInputKeys frame) :
    ∀ key ∈ frameWorkKeys frame, key ≠ observed := by
  intro key written same
  exact List.disjoint_left.mp (frame_work_input_disjoint frame) written (same.symm ▸ originalInput)

private def NamedDriverPreservesRead (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {shape : CShape} (observed : CStorageRef ctx shape) : Prop :=
  let chosen := namedDriverInstrument parameters frame spec row environment
  letI : Fintype chosen.1 := chosen.2.1
  ∀ original outcome, (chosen.2.2.record original outcome).1.1.read (.storage observed) =
    original.1.read (.storage observed)

attribute [local irreducible] NamedDriverPreservesRead

/-- The specified actual Driver retains every caller read separate from its persistent writes. -/
lemma namedDriverInstrument_read_separate (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {shape : CShape} (observed : CStorageRef ctx shape)
    (workFree : ∀ key ∈ frameWorkKeys frame, key ≠ observed.key)
    (outputFree : ∀ bit, (parameters.output bit).key ≠ observed.key)
    (maskFree : parameters.mask.key ≠ observed.key)
    (parityFree : ∀ bit, (parameters.parity bit).key ≠ observed.key)
    (temporaryFree : parameters.temporary.key ≠ observed.key) :
    NamedDriverPreservesRead parameters frame spec row environment observed := by
  unfold NamedDriverPreservesRead
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
      apply tablePrefixInstrument_read_separate (ctx := inner) (services := services)
      · exact constructed_table_read_free frame lift cells distinct separated row observed workFree
      · exact (Driver.kernelParameters parameters lift
          (quantumLayout_wires_of_quantumWires same)
          (frame.tableFrame lift cells distinct separated row).arrays).pointProgramInstrument_read
            environment (.storage (lift.liftStorage observed))
            (fun bit => transported_read_free lift _ observed (outputFree bit))
            (transported_read_free lift _ observed maskFree)
            (fun bit => transported_read_free lift _ observed (parityFree bit))
            (transported_read_free lift _ observed temporaryFree))

private lemma write_shape_key_ne {written read : CShape} (output : CWriteRef ctx written)
    (observed : CStorageRef ctx read) (different : written ≠ read) :
    output.key ≠ observed.key := fun same => different
  (CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef observed same)

/-- Original unsigned-word reads need separation only from the four persistent working words. -/
lemma namedDriverInstrument_word_read (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width : Nat} (observed : CStorageRef ctx (.unsignedWord width))
    (workFree : ∀ key ∈ frameWorkKeys frame, key ≠ observed.key) :
    NamedDriverPreservesRead parameters frame spec row environment observed := by
  apply namedDriverInstrument_read_separate parameters frame spec row environment observed workFree
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact write_shape_key_ne _ observed (by intro impossible; cases impossible)

/-- The modulus and three persistent input constants retain their original stored words. -/
lemma namedDriverInstrument_frame_word_read (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width : Nat} (observed : CStorageRef ctx (.unsignedWord width))
    (originalInput : observed.key ∈ frameInputKeys frame) :
    NamedDriverPreservesRead parameters frame spec row environment observed := by
  apply namedDriverInstrument_word_read
  exact frame_work_read_free frame observed.key originalInput

/-- Every original word array survives, retaining all future base rows at once. -/
lemma namedDriverInstrument_array_read (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width length : Nat} (observed : CStorageRef ctx (.fixedVector length (.unsignedWord width))) :
    NamedDriverPreservesRead parameters frame spec row environment observed := by
  apply namedDriverInstrument_read_separate
  · intro key written
    simp only [frameWorkKeys, List.mem_cons, List.not_mem_nil, or_false] at written
    rcases written with rfl | rfl | rfl | rfl
    all_goals exact write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact write_shape_key_ne _ observed (by intro impossible; cases impossible)

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
