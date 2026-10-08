/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Sixteen declared EH observations in one physical bank

The real residue draw and parameter preparation precede the sole quantum-bank
preparation. The first observation uses that prepared bank. Each later
observation pays for reset of the same bank, then performs one selected query,
measurement and two physical bit-packing operations. Later batches overwrite
the source, parameter and sample cells without reallocating the quantum bank.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The second actual pack of measured exponent cells into one sample slot. -/
def copyOp (index : Fin 16) :
    ClassicalOp (.fixedVector (measurementBits N) (.finite 2))
      (.bits (measurementBits N)) (context base noQuantum N)
        (context base noQuantum N) :=
  .packFiniteBits (measurementBits N)
    (context base noQuantum N)
    (.fixedVector fun position =>
      .storage (Native.cells (storageContext base N)
        (storage_empty base noQuantum N) N position).toCStorageRef)
    (terminalRef base noQuantum N index)

/-- Pay for that pack in the declared classical operation model. -/
def copy (index : Fin 16) :
    Circuit (model input) (context base noQuantum N) (context base noQuantum N) :=
  BitWord.instruction (execution := model input) (copyOp base noQuantum N index)

/-- A later observation resets, queries, measures, packs and saves one sample. -/
def reusedSample (index : Fin 16) :
    Circuit (model input) (context base noQuantum N) (context base noQuantum N) :=
  .seq (reuse (storageContext base N) (storage_empty base noQuantum N)
    N input (parameter base N))
    (copy base noQuantum N input index)

/-- The prepared first observation is followed by fifteen paid resets. -/
def firstBatch :
    Circuit (model input) (context base noQuantum N) (context base noQuantum N) :=
  .seq
    (.seq (body (storageContext base N) (storage_empty base noQuantum N)
      N input (parameter base N)) (copy base noQuantum N input 0))
    (Circuit.forRange 15 fun index =>
      reusedSample base noQuantum N input index.succ)

/-- Redraw the actual source and recompute the retained complete parameter. -/
def redraw :
    Circuit (model input) (context base noQuantum N) (context base noQuantum N) :=
  .seq (ShorStyle.Canonical.Sampler.PackedSample.draw
    (model := model input) N (sourceRef base noQuantum N))
    (ShorStyle.Canonical.Sampler.Program.circuit
      (model := model input) N
      (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N))

/-- A further batch pays for all sixteen resets in the same live context. -/
def nextBatch :
    Circuit (model input) (context base noQuantum N) (context base noQuantum N) :=
  .seq (redraw base noQuantum N input)
    (Circuit.forRange 16 (reusedSample base noQuantum N input))

/-- Retain the source, parameter and results before preparing the only bank. -/
def setup : Circuit (model input) base (context base noQuantum N) :=
  .seq (ShorStyle.Canonical.Sampler.Retained.circuit (model := model input) base N)
    (.seq (Native.Batch.Slots.allocate (model := model input) (sourceContext base N) N)
      (.seq (Declared.prepare (storageContext base N)
          (storage_empty base noQuantum N) N input)
        (Declared.allocate (storageContext base N)
          (storage_empty base noQuantum N) N input)))

/-- Execute the complete first sixteen observations on the actual live bank. -/
def code : Circuit (model input) base (context base noQuantum N) :=
  .seq (setup base noQuantum N input) (firstBatch base noQuantum N input)

/-- Return all actual sample cells while retaining every live context entry. -/
def run : AlgorithmRun (model input) base (context base noQuantum N)
    (.fixedVector 16 (.bits (measurementBits N))) where
  code := code base noQuantum N input
  output := Output.all (context base noQuantum N)
    (.read (.fixedVector fun index =>
      .storage (terminalRef base noQuantum N index).toCStorageRef))

/-- The batch output lists every actual source, parameter, result and bank key. -/
theorem output_listing :
    (run base noQuantum N input).output.listing =
      (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
