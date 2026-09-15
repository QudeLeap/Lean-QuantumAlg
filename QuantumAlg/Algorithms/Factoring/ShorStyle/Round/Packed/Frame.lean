/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Packed
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame

/-!
# Earlier stored Shor values survive the actual phase writes

Only the actual finite result cells and packed-output cell are written by
this fragment. Earlier structural inputs therefore keep their complete
values and can be observed jointly with the new source phase result.
The surrounding actual allocation supplies the separation proofs.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
  (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (phaseBits N)))

/-- Actual phase writes preserve all earlier structural inputs on separate keys. -/
theorem packed_read_preserved {shape : CShape} (input : CInputRef ctx shape)
    (cellsSeparate : ∀ index, (cells index).key ∉ input.storageKeys)
    (resultSeparate : result.key ∉ input.storageKeys)
    (store : Store ctx) (basis : ctx.register.Index) :
    (packedBasisStore N sameWires cells result store basis).read input = store.read input := by
  have separate : ∀ item ∈ readouts N sameWires cells,
      item.output.key ∉ input.storageKeys := by
    intro item present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    intro member
    exact cellsSeparate index ((readout_key N sameWires cells index) ▸ member)
  exact (Store.read_applyOp_of_not_mem_storageKeys
    (Circuit.writeMeasurementPath (readouts N sameWires cells) store
      (Circuit.measurementBasisPath (readouts N sameWires cells) basis))
    (packing N cells result) input resultSeparate).trans
    (Circuit.writeMeasurementPath_read_input (readouts N sameWires cells) input separate store _)

/-- The actual joint read retains earlier values together with the new source phase outcome. -/
theorem packed_joint_read {shape : CShape} (input : CInputRef ctx shape)
    (distinct : Function.Injective (fun index => (cells index).key))
    (cellsSeparate : ∀ index, (cells index).key ∉ input.storageKeys)
    (resultSeparate : result.key ∉ input.storageKeys)
    (store : Store ctx) (basis : ctx.register.Index) :
    (packedBasisStore N sameWires cells result store basis).read
        (.product input (.storage result.toCStorageRef)) =
      CShape.Value.product (store.read input)
        (.bits ((OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
          (NativePlacement.basisEquiv N sameWires basis))) :=
  congrArg₂ CShape.Value.product
    (packed_read_preserved N sameWires cells result input cellsSeparate resultSeparate store basis)
    (packed_output N sameWires cells result distinct store basis)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
