/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Fixed classical storage for the original oracle batch

Sixteen actual bit-string cells retain the measured samples, and one separate
optional word receives classical recovery. These cells are allocated before
the single quantum bank. Later samples overwrite the same cells. Structural
reference lifting performs no runtime copy and creates no additional storage.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Slots

open Execution

variable {kind : ProblemKind}

/-- Retain each sample cell before any oracle bank is prepared. -/
@[implicit_reducible]
def samples (ctx : RuntimeCtx kind) (width : Nat) : Nat → RuntimeCtx kind
  | 0 => ctx
  | count + 1 =>
      (samples ctx width count).addRetained (samples ctx width count).canonicalFreshKey
        (.bits width) (samples ctx width count).canonicalFreshKey_fresh

/-- The newest allocated sample cell is index zero. -/
@[implicit_reducible]
def sampleRef (ctx : RuntimeCtx kind) (width : Nat) :
    (count : Nat) → Fin count → CWriteRef (samples ctx width count) (.bits width)
  | 0, index => Fin.elim0 index
  | count + 1, index =>
      Fin.cases
        (CWriteRef.retainedHead (samples ctx width count)
          (samples ctx width count).canonicalFreshKey (.bits width)
          (samples ctx width count).canonicalFreshKey_fresh)
        (fun previous => (sampleRef ctx width count previous).underRetained
          (samples ctx width count).canonicalFreshKey (.bits width)
          (samples ctx width count).canonicalFreshKey_fresh) index

/-- Every earlier writable cell remains the same cell under the sample allocations. -/
def liftSamples {ctx : RuntimeCtx kind} {shape : CShape} (width : Nat)
    (ref : CWriteRef ctx shape) : (count : Nat) → CWriteRef (samples ctx width count) shape
  | 0 => ref
  | count + 1 =>
      (liftSamples width ref count).underRetained (samples ctx width count).canonicalFreshKey
        (.bits width) (samples ctx width count).canonicalFreshKey_fresh

/-- Each sample cell is allocated by the actual retention instruction. -/
@[implicit_reducible]
def allocateSamples {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
    (width : Nat) : (count : Nat) → Circuit model ctx (samples ctx width count)
  | 0 => .id ctx
  | count + 1 =>
      .seq (allocateSamples ctx width count)
        (.retain (samples ctx width count) (samples ctx width count).canonicalFreshKey
          (.bits width) (samples ctx width count).canonicalFreshKey_fresh)

/-- All sixteen terminal samples and the original optional factor result stay live. -/
def context (ctx : RuntimeCtx kind) (N : Nat) : RuntimeCtx kind :=
  (samples ctx (measurementBits N) 16).addRetained
    (samples ctx (measurementBits N) 16).canonicalFreshKey
    (.option (.unsignedWord (modulusBits N)))
    (samples ctx (measurementBits N) 16).canonicalFreshKey_fresh

/-- An actual sample slot, lifted past the separate factor result. -/
def terminalRef (ctx : RuntimeCtx kind) (N : Nat) (index : Fin 16) :
    CWriteRef (context ctx N) (.bits (measurementBits N)) :=
  (sampleRef ctx (measurementBits N) 16 index).underRetained
    (samples ctx (measurementBits N) 16).canonicalFreshKey
    (.option (.unsignedWord (modulusBits N)))
    (samples ctx (measurementBits N) 16).canonicalFreshKey_fresh

/-- The real optional factor cell is separate from all sample slots. -/
def factorRef (ctx : RuntimeCtx kind) (N : Nat) :
    CWriteRef (context ctx N) (.option (.unsignedWord (modulusBits N))) :=
  CWriteRef.retainedHead (samples ctx (measurementBits N) 16)
    (samples ctx (measurementBits N) 16).canonicalFreshKey
    (.option (.unsignedWord (modulusBits N)))
    (samples ctx (measurementBits N) 16).canonicalFreshKey_fresh

/-- Lift earlier writable source and parameter cells beneath every fixed batch slot. -/
def liftWrite {ctx : RuntimeCtx kind} {shape : CShape} (N : Nat)
    (ref : CWriteRef ctx shape) : CWriteRef (context ctx N) shape :=
  (liftSamples (measurementBits N) ref 16).underRetained
    (samples ctx (measurementBits N) 16).canonicalFreshKey
    (.option (.unsignedWord (modulusBits N)))
    (samples ctx (measurementBits N) 16).canonicalFreshKey_fresh

/-- All seventeen batch cells are initialized by their actual retention instructions. -/
def allocate {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat) :
    Circuit model ctx (context ctx N) :=
  .seq (allocateSamples (model := model) ctx (measurementBits N) 16)
    (.retain (samples ctx (measurementBits N) 16)
      (samples ctx (measurementBits N) 16).canonicalFreshKey
      (.option (.unsignedWord (modulusBits N)))
      (samples ctx (measurementBits N) 16).canonicalFreshKey_fresh)

/-- Real sample retention does not change the caller's quantum wires. -/
lemma nativeOracle_sampleSlots_wires (ctx : RuntimeCtx kind) (width count : Nat) :
    (samples ctx width count).quantumWires = ctx.quantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [samples, RuntimeCtx.quantumWires_addRetained] using ih

/-- The full fixed batch storage contributes no quantum system. -/
lemma nativeOracle_batchSlots_wires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := by
  rw [context, RuntimeCtx.quantumWires_addRetained]
  exact nativeOracle_sampleSlots_wires ctx (measurementBits N) 16

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Slots
