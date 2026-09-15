/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Packed
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual packed writes preserve earlier stored inputs

The measured finite cells and the new packed-result cell are the only writes
in this part of the round. Structural inputs supported on the earlier keys
therefore keep their complete values. Together with the actual output-read
theorem, this identifies the joint observation of earlier data and the newly
measured source outcome. The surrounding retained layout supplies the key
separation; it is not an added endpoint input-state assumption.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

private theorem measured_input {ctx : RuntimeCtx .quantum} {shape : CShape}
    (readouts : List (ZReadout ctx)) (input : CInputRef ctx shape)
    (separate : ∀ item ∈ readouts, item.output.key ∉ input.storageKeys)
    (store : Store ctx) (path : (Circuit.measurementSequence readouts).Path) :
    (Circuit.writeMeasurementPath readouts store path).read input = store.read input := by
  induction readouts generalizing store with
  | nil => rfl
  | cons head tail induction =>
      exact (induction (fun item present => separate item (.tail head present))
        (store.write head.output (.finite path.1)) path.2).trans
        (Store.read_write_of_not_mem_storageKeys store head.output (.finite path.1)
          input (separate head (.head tail)))

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (resultBits m ell width)))

/-- The actual measured writes and packed output retain every structurally separate input. -/
theorem shortDLP_runtimePacked_read_preserved {shape : CShape} (input : CInputRef ctx shape)
    (cellsSeparate : ∀ index, (cells index).key ∉ input.storageKeys)
    (resultSeparate : result.key ∉ input.storageKeys)
    (store : Store ctx) (basis : ctx.register.Index) :
    (packedBasisStore m ell width sameWires cells result store basis).read input =
      store.read input := by
  have separate : ∀ item ∈ readouts m ell width sameWires cells,
      item.output.key ∉ input.storageKeys := by
    intro item present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    intro member
    exact cellsSeparate index
      ((shortDLP_runtimeReadout_key m ell width sameWires cells index) ▸ member)
  exact (Store.read_applyOp_of_not_mem_storageKeys
    (Circuit.writeMeasurementPath (readouts m ell width sameWires cells) store
      (Circuit.measurementBasisPath (readouts m ell width sameWires cells) basis))
    (packing m ell width cells result) input resultSeparate).trans
    (measured_input (readouts m ell width sameWires cells) input separate store _)

/-- The actual joint read combines unchanged earlier data with the source measurement outcome. -/
theorem shortDLP_runtimePacked_joint_read {shape : CShape} (input : CInputRef ctx shape)
    (distinct : Function.Injective (fun index => (cells index).key))
    (cellsSeparate : ∀ index, (cells index).key ∉ input.storageKeys)
    (resultSeparate : result.key ∉ input.storageKeys)
    (store : Store ctx) (basis : ctx.register.Index) :
    (packedBasisStore m ell width sameWires cells result store basis).read
        (.product input (.storage result.toCStorageRef)) =
      CShape.Value.product (store.read input)
        (.bits ((ShortDLP.measurement (registerParameters m ell width)).readout
          (RuntimePlacement.basisEquiv m ell width sameWires basis))) :=
  congrArg₂ CShape.Value.product
    (shortDLP_runtimePacked_read_preserved m ell width sameWires cells result input
      cellsSeparate resultSeparate store basis)
    (shortDLP_runtimePacked_output m ell width sameWires cells result distinct store basis)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
