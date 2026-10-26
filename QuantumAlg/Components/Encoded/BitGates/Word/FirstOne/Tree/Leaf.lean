/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree

/-! # Exact full-state leaf action of the original paid Toffoli mask -/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- A real leaf xors its public mask precisely under its retained enable and original source bit. -/
lemma leafGates_step (label : Fin count) (current : Fin (depth + 1)) (state : Data) :
    GateSpec.stepList
      (Word.doubleControlledXorConstantGates (frame.stack.bit current) (frame.source.bit label)
        frame.output (leafMask (outputWidth := outputWidth) label)
        (Ne.symm (frame.sourceStack label current))
        (fun output => Ne.symm (frame.outputStack output current))
        (fun output => frame.sourceOutput label output)) state =
      if (frame.stack.bit current).get state && (frame.source.bit label).get state then
        Word.xorConstantStep frame.output (leafMask (outputWidth := outputWidth) label) state
      else state := by
  unfold Word.doubleControlledXorConstantGates Word.xorConstantStep Word.xorConstantGates
  generalize Word.constantOneIndices (leafMask (outputWidth := outputWidth) label) = indices
  induction indices generalizing state with
  | nil => split <;> rfl
  | cons index rest ih =>
      have enableRead : ∀ value,
          (frame.stack.bit current).get ((frame.output.bit index).flip value) =
            (frame.stack.bit current).get value :=
        get_flip_of_wire_ne _ _ (frame.outputStack index current)
      have sourceRead : ∀ value,
          (frame.source.bit label).get ((frame.output.bit index).flip value) =
            (frame.source.bit label).get value :=
        get_flip_of_wire_ne _ _ (Ne.symm (frame.sourceOutput label index))
      cases enabled : (frame.stack.bit current).get state <;>
        cases marked : (frame.source.bit label).get state
      · simpa only [List.map_cons, GateSpec.stepList, GateSpec.step, toffoliStep,
          enabled, marked, Bool.false_and, Bool.false_eq_true, if_false] using ih state
      · simpa only [List.map_cons, GateSpec.stepList, GateSpec.step, toffoliStep,
          enabled, marked, Bool.false_and, Bool.false_eq_true, if_false] using ih state
      · simpa only [List.map_cons, GateSpec.stepList, GateSpec.step, toffoliStep,
          enabled, marked, Bool.true_and, Bool.false_eq_true, if_false] using ih state
      · simpa only [List.map_cons, GateSpec.stepList, GateSpec.step, toffoliStep,
          enableRead, sourceRead, enabled, marked, Bool.true_and, if_true] using
            ih ((frame.output.bit index).flip state)

end

end QuantumAlg.EncodedBit.FirstOne.Frame
