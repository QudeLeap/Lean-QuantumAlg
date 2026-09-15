/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Readout
import all QuantumAlg.Core.Execution.Measured.Classical

/-!
# Actual Shor packed results jointly with the reference

The store expression below records the existing Z writes and the real
packing opcode's subsequent write. Its readout is the source phase result,
and each complete resulting store retains its actual reference fiber.
The store expression is a mathematical description of those instructions;
it does not supply a measurement outcome or introduce an execution step.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
  (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (phaseBits N)))

/-- The existing Z-write sequence followed by the actual packing output write on one basis fiber. -/
def packedBasisStore (store : Store ctx) (basis : ctx.register.Index) : Store ctx :=
  (Circuit.writeMeasurementPath (readouts N sameWires cells) store
    (Circuit.measurementBasisPath (readouts N sameWires cells) basis)).applyOp
      (packing N cells result)

/-- The actual packed cell reads precisely the original source phase outcome. -/
theorem packed_output (distinct : Function.Injective (fun index => (cells index).key))
    (store : Store ctx) (basis : ctx.register.Index) :
    (packedBasisStore N sameWires cells result store basis).read
        (.storage result.toCStorageRef) =
      CShape.Value.bits
        ((OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
          (NativePlacement.basisEquiv N sameWires basis)) :=
  (Store.read_applyOp_output
    (Circuit.writeMeasurementPath (readouts N sameWires cells) store
      (Circuit.measurementBasisPath (readouts N sameWires cells) basis))
    (packing N cells result)).trans
      (packing_measured_value N sameWires cells distinct result store basis)

/-- Each observation of the real measured and packed store retains its complete reference fiber. -/
theorem packed_reference_entry
    {Reference : Register} {History Observed : Type} [Fintype History] [Fintype Observed]
    (state : State ctx Reference History) (observe : Store ctx → Observed) (value : Observed)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      DensityOperator.matrix
        ((ExecutionState.mapClassical
          ((Circuit.seq (Circuit.measurementSequence (readouts N sameWires cells))
            (.classical (packing N cells result))).execute Reference state)
          (fun entry => observe entry.1)).block value) (basis, left) (basis, right)) =
      ExecutionState.referenceFiberSum state (fun original basis =>
        if observe (packedBasisStore N sameWires cells result original.1 basis) = value
        then 1 else 0) left right :=
  Circuit.measurementSequence_classical_reference_entry (readouts N sameWires cells)
    (packing N cells result) state observe value left right

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
