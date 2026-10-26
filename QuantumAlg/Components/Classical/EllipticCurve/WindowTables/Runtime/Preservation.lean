/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Runtime.Values
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Instrument
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Store
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Phase.Comparison

/-!
# All constructed columns survive every actual runtime unlookup record

Real finite measurement writes, packed masks and paid parity work have
closed shapes different from every complete table array. Every physical
outcome therefore retains all five original array values for the next
query, independently of the actual quantum state or old Store contents.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution EncodedBit EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}
  (tables : TableFrame ctx wordWidth (2 ^ (highRemaining + lowWidth + 1)))
  (frame : UnlookupFrame encoding wordWidth lowWidth highRemaining)
  (physical : QubitLayout encoding.width)
  (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
  (output : Fin wordWidth → CWriteRef ctx (.finite 2))
  (mask : CWriteRef ctx (.bits wordWidth))
  (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)

private lemma differentKey {firstShape secondShape : CShape}
    (first : CWriteRef ctx firstShape) (second : CWriteRef ctx secondShape)
    (different : firstShape ≠ secondShape) : first.key ≠ second.key := by
  intro equal
  exact different (CStorageRef.storageRef_shape_eq_of_key
    first.toCStorageRef second.toCStorageRef equal)

/-- The true final Store of every physical outcome retains every complete constructed column. -/
lemma unlookupRecord_read_column (column observed : Fin 5) (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path) :
    (RuntimeUnlookup.record frame (services := services) physical sameWires
      output mask parity temporary (RuntimeTable.splitInputs (tables.runtimeSource column))
      store path).1.read (tables.runtimeSource observed) =
        store.read (tables.runtimeSource observed) := by
  let source := RuntimeTable.splitInputs (tables.runtimeSource column)
  let reading := tables.runtimeSource observed
  have outputFree (index : Fin wordWidth) : (output index).key ∉ reading.storageKeys := by
    change (output index).key ∉ [(tables.finishColumns observed).key]
    simpa only [List.mem_singleton] using
      differentKey (output index) (tables.finishColumns observed) (by intro same; cases same)
  have maskFree : mask.key ∉ reading.storageKeys := by
    change mask.key ∉ [(tables.finishColumns observed).key]
    simpa only [List.mem_singleton] using
      differentKey mask (tables.finishColumns observed) (by intro same; cases same)
  have parityFree (index : Fin (2 ^ lowWidth)) : (parity index).key ∉ reading.storageKeys := by
    change (parity index).key ∉ [(tables.finishColumns observed).key]
    simpa only [List.mem_singleton] using
      differentKey (parity index) (tables.finishColumns observed) (by intro same; cases same)
  have temporaryFree : temporary.key ∉ reading.storageKeys := by
    change temporary.key ∉ [(tables.finishColumns observed).key]
    simpa only [List.mem_singleton] using
      differentKey temporary (tables.finishColumns observed) (by intro same; cases same)
  let reset := RuntimeUnlookup.resetRecord frame (services := services)
    physical sameWires output mask store path
  have resetReading : reset.1.read reading = store.read reading := by
    exact measuredWordFinalStore_read_other (oracles := .empty) (services := services)
      physical sameWires frame.result output mask reading outputFree maskFree store path
  let left := RuntimeUnlookup.halfRecord frame (services := services) physical sameWires
    (.storage mask.toCStorageRef) parity temporary (source false) reset.1
  have first := RuntimeUnlookup.halfRecord_read_other (services := services)
    frame physical sameWires
    (.storage mask.toCStorageRef) parity temporary (source false) reading
    parityFree temporaryFree reset.1
  have second := RuntimeUnlookup.halfRecord_read_other (services := services)
    frame physical sameWires
    (.storage mask.toCStorageRef) parity temporary (source true) reading
    parityFree temporaryFree left.1
  exact second.trans (first.trans resetReading)

/-- The original canonical point-word table remains available after every actual paid record. -/
lemma unlookupRecord_tableValue (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec wordWidth)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (column : Fin 5) (store : Store ctx) (values : TableValue curve tables point store)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires frame.result output)).Path) :
    TableValue curve tables point
      (RuntimeUnlookup.record frame (services := services) physical sameWires
        output mask parity temporary (RuntimeTable.splitInputs (tables.runtimeSource column))
        store path).1 := by
  intro row observed
  have unchanged := tables.unlookupRecord_read_column frame physical sameWires
    output mask parity temporary column observed store path
  exact (congrArg (fun stored :
      CShape.Value (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)) =>
        stored.get row) unchanged).trans (values row observed)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
