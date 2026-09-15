/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Sequence
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import Mathlib.Data.List.OfFn

/-!
# Reset all existing qubits through one actual result cell

The wire list contains each existing physical system once. Every measurement
writes the same finite two-valued cell, and the existing reset circuit reads
that cell to select its declared cyclic correction. Earlier values of this
scratch cell are overwritten; no quantum system or classical cell is allocated.

The complete Output lists the unchanged live context and reads the scratch
cell. An empty bank emits no events and preserves that cell's incoming value.
The independent budget contains both correction alternatives for every wire;
each actual path executes only its selected correction, including zero.
-/

namespace QuantumAlg.ZReset.Bank

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum}

private def resultAt (dimension : ℕ+) (equal : dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) : CWriteRef ctx (.finite dimension) :=
  equal.symm ▸ scratch

private theorem resultAt_key (dimension : ℕ+) (equal : dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) :
    (resultAt dimension equal scratch).key = scratch.key := by
  cases equal
  rfl

/-- Enumerate every physical qubit once, reusing the same writable result cell. -/
def readouts (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) : List (ZReadout ctx) :=
  List.ofFn (fun wire =>
    ⟨wire, resultAt (ctx.quantumLayout.wire wire).dimension (qubits wire) scratch⟩)

/-- Reset the existing bank using only the actual measurement-and-correction sequence. -/
def code (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) : Circuit ctx ctx :=
  sequence (readouts qubits scratch)

/-- Retain every live key and expose the actual final contents of the shared result cell. -/
def output (scratch : CWriteRef ctx (.finite 2)) : Output ctx (.finite 2) :=
  Output.all ctx (.read (.storage scratch.toCStorageRef))

/-- The real reset syntax together with its complete live-resource manifest. -/
def run (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) : AlgorithmRun ctx ctx (.finite 2) where
  code := code qubits scratch
  output := output scratch

/-- Independent native coordinates include each possible correction for each qubit. -/
def envelope (width : Nat) : ResourcePool .quantum := width • eventEnvelope 2

/-- The actual readout count is the physical system count, including width zero. -/
theorem zResetBank_readouts_length (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) :
    (readouts qubits scratch).length = ctx.systemCount := by
  exact List.length_ofFn

/-- Coverage is proved from the constructed list, rather than supplied by a reset caller. -/
theorem zResetBank_readouts_cover (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (wire : Fin ctx.systemCount) :
    wire ∈ (readouts qubits scratch).map ZReadout.wire := by
  unfold readouts
  rw [List.map_ofFn]
  exact List.mem_ofFn.mpr ⟨wire, rfl⟩

/-- Every actual measurement writes precisely the one shared scratch key. -/
theorem zResetBank_readouts_key (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (item : ZReadout ctx)
    (present : item ∈ readouts qubits scratch) : item.output.key = scratch.key := by
  obtain ⟨wire, rfl⟩ := List.mem_ofFn.mp present
  exact resultAt_key _ (qubits wire) scratch

/-- The dimension-indexed list envelope is exactly the independent width budget. -/
theorem zResetBank_envelope (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) :
    sequenceEnvelope (readouts qubits scratch) = envelope ctx.systemCount := by
  unfold sequenceEnvelope readouts
  rw [List.map_ofFn]
  change (List.ofFn (fun wire : Fin ctx.systemCount =>
    eventEnvelope (ctx.quantumLayout.wire wire).dimension)).sum = _
  simp only [qubits, List.ofFn_const, List.sum_replicate, envelope]

/-- Every actual path is bounded coordinatewise by the independently repeated envelope. -/
theorem zResetBank_resourcePool_le (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (path : (code qubits scratch).Path) :
    (code qubits scratch).resourcePool path ≤ envelope ctx.systemCount :=
  (zReset_sequence_resourcePool_le (readouts qubits scratch) path).trans_eq
    (zResetBank_envelope qubits scratch)

/-- Exact actual events count one Z measurement and one selected correction per qubit. -/
theorem zResetBank_eventTrace_length (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (path : (code qubits scratch).Path) :
    ((code qubits scratch).eventTrace path).length = 2 * ctx.systemCount :=
  (zReset_sequence_eventTrace_length (readouts qubits scratch) path).trans
    (congrArg (2 * ·) (zResetBank_readouts_length qubits scratch))

/-- Exact unit duration includes the real measurement-to-correction dependencies. -/
theorem zResetBank_unitDepth (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (path : (code qubits scratch).Path) :
    (code qubits scratch).depth (fun _ => 1) path = 2 * ctx.systemCount :=
  (zReset_sequence_unitDepth (readouts qubits scratch) path).trans
    (congrArg (2 * ·) (zResetBank_readouts_length qubits scratch))

/-- Resident space is exactly the original bank, scratch and earlier retained results. -/
theorem zResetBank_peakResidentSpace (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (path : (code qubits scratch).Path) :
    (code qubits scratch).peakResidentSpace path = ctx.residentSpace :=
  zReset_sequence_peakResidentSpace (readouts qubits scratch) path

/-- Auxiliary accounting preserves the actual original roles without adding a new bank. -/
theorem zResetBank_peakAuxiliarySpace (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (path : (code qubits scratch).Path) :
    (code qubits scratch).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  zReset_sequence_peakAuxiliarySpace (readouts qubits scratch) path

/-- The complete output manifest includes the bank and the actual shared scratch cell. -/
theorem zResetBank_output_listing (scratch : CWriteRef ctx (.finite 2)) :
    (output scratch).listing = ctx.keys := rfl

end

end QuantumAlg.ZReset.Bank
