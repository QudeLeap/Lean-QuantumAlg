/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import all QuantumAlg.Core.Execution.Store.WritePrefix
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# All actual Fourier outcome cells

The parent extends the existing context with n distinct retained binary cells.
The child uses those real writable references without allocating. Physical
outcome tuples and decoded frequency labels remain mathematical observations
of those cells, rather than an uncharged runtime integer-packing instruction.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum}

/-- Dimension transport preserves the same writable physical storage identity. -/
def castBinaryOutput {first second : ℕ+} (same : first = second)
    (output : CWriteRef ctx (.finite second)) : CWriteRef ctx (.finite first) :=
  same.symm ▸ output

lemma castBinaryOutput_key {first second : ℕ+} (same : first = second)
    (output : CWriteRef ctx (.finite second)) :
    (castBinaryOutput same output).key = output.key := by
  cases same
  rfl

/-- Existing physical wires pass unchanged under the parent's n retained binary cells. -/
def canonicalOutcomeWires {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount) :
    Fin n ↪ Fin (MeasurementCells.context ctx 2 n).systemCount :=
  wires.trans (MeasurementCells.wireEquiv ctx 2 n).toEmbedding

lemma canonicalOutcomeQubits {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) (index : Fin n) :
    ((MeasurementCells.context ctx 2 n).quantumLayout.wire
      (canonicalOutcomeWires wires index)).dimension = 2 := by
  change ((MeasurementCells.context ctx 2 n).quantumLayout.wire
    (MeasurementCells.wireEquiv ctx 2 n (wires index))).dimension = 2
  rw [MeasurementCells.wireEquiv_preserved]
  exact qubits index

/-- One genuine fresh binary result cell for every selected physical Fourier wire. -/
def canonicalOutcomeOutputs {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) (index : Fin n) :
    CWriteRef (MeasurementCells.context ctx 2 n)
      (.finite ((MeasurementCells.context ctx 2 n).quantumLayout.wire
        (canonicalOutcomeWires wires index)).dimension) :=
  castBinaryOutput (canonicalOutcomeQubits wires qubits index)
    (MeasurementCells.reference ctx 2 n index)

/-- Result independence is proved at actual storage keys, including across ownership roles. -/
lemma canonicalOutcomeOutputs_distinct {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2) :
    Function.Injective (fun index => (canonicalOutcomeOutputs wires qubits index).key) := by
  intro left right equal
  apply MeasurementCells.reference_key_injective ctx 2 n
  simpa only [canonicalOutcomeOutputs, castBinaryOutput_key] using equal

/-- Physical tuple bits are read in existing source big-endian coordinates. -/
def outcomeValues {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outcome : Bits n) (index : Fin n) :
    CShape.Value (.finite (ctx.quantumLayout.wire (wires index)).dimension) :=
  .finite (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits index)).symm
    (tupleCoordinates n outcome index))

/-- The literal head measurement writes the recursive physical head bit. -/
lemma outcomeValues_head {n : Nat} (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (head : Fin 2) (tail : Bits n) :
    outcomeValues wires qubits (head, tail) 0 =
      .finite (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm head) := by
  simp only [outcomeValues, tupleCoordinates_head]

/-- The remaining literal measurement values are exactly the recursive tail values. -/
lemma outcomeValues_tail {n : Nat} (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (head : Fin 2) (tail : Bits n) (index : Fin n) :
    let tailWires : Fin n ↪ Fin ctx.systemCount :=
      ⟨fun i => wires i.succ, fun _ _ same => Fin.succ_injective n (wires.injective same)⟩
    outcomeValues wires qubits (head, tail) index.succ =
      outcomeValues tailWires (fun i => qubits i.succ) tail index := by
  simp only [outcomeValues, tupleCoordinates_tail]

/-- The full original store after the n literal measurement writes, without packing. -/
def outcomeStore {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    (original : Store ctx) (outcome : Bits n) : Store ctx :=
  Store.writePrefix outputs (outcomeValues wires qubits outcome) original n le_rfl

/-- Native recursion and the full outcome store perform the identical ordered real writes. -/
lemma outcomeStore_head_tail {n : Nat}
    (wires : Fin (n + 1) ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    (original : Store ctx) (head : Fin 2) (tail : Bits n) :
    let tailWires : Fin n ↪ Fin ctx.systemCount :=
      ⟨fun i => wires i.succ, fun _ _ same => Fin.succ_injective n (wires.injective same)⟩
    outcomeStore wires qubits outputs original (head, tail) =
      outcomeStore tailWires (fun i => qubits i.succ) (fun i => outputs i.succ)
        (original.write (outputs 0)
          (.finite (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (qubits 0)).symm head)))
        tail := by
  dsimp only [outcomeStore]
  rw [Store.writePrefix_all_head_tail]
  simp only [outcomeValues_head, outcomeValues_tail]

/-- Every outcome remains in its own actual cell after the entire ordered write sequence. -/
lemma outcomeStore_read {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    (separate : Function.Injective (fun index => (outputs index).key))
    (original : Store ctx) (outcome : Bits n) (index : Fin n) :
    (outcomeStore wires qubits outputs original outcome).read
      (.storage (outputs index).toCStorageRef) = outcomeValues wires qubits outcome index :=
  Store.read_writePrefix_all outputs (outcomeValues wires qubits outcome)
    separate original index

/-- The canonical parent layout supplies the separation proof internally. -/
lemma canonicalOutcomeStore_read {n : Nat} (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (original : Store (MeasurementCells.context ctx 2 n))
    (outcome : Bits n) (index : Fin n) :
    (outcomeStore (canonicalOutcomeWires wires) (canonicalOutcomeQubits wires qubits)
      (canonicalOutcomeOutputs wires qubits) original outcome).read
        (.storage (canonicalOutcomeOutputs wires qubits index).toCStorageRef) =
      outcomeValues (canonicalOutcomeWires wires) (canonicalOutcomeQubits wires qubits)
        outcome index :=
  outcomeStore_read (canonicalOutcomeWires wires) (canonicalOutcomeQubits wires qubits)
    (canonicalOutcomeOutputs wires qubits) (canonicalOutcomeOutputs_distinct wires qubits)
    original outcome index

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
