/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Parallel.Resources

/-! # Two complete physical barrel words under the same retained metadata controls -/

namespace QuantumAlg.EncodedBit.PermutationBarrelParallel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size controls : Nat}

/-- The second word is separate from the first complete barrel and every original control. -/
structure Frame (encoding : BinaryLabelEncoding Data) (size controls : Nat) where
  left : PermutationBarrel encoding size controls
  rightBit : Fin size → EncodedBit encoding
  rightDistinct : Function.Injective (fun index => (rightBit index).wire)
  cross : ∀ i j, (left.bit i).wire ≠ (rightBit j).wire
  rightControl : ∀ i j, (left.control i).wire ≠ (rightBit j).wire

namespace Frame

def rightBarrel (frame : Frame encoding size controls) :
    PermutationBarrel encoding size controls where
  bit := frame.rightBit
  control := frame.left.control
  distinct := frame.rightDistinct
  separate := frame.rightControl

def pairFrame (frame : Frame encoding size controls) (index : Fin controls) :
    PermutationParallel.Frame encoding size where
  control := frame.left.control index
  left := frame.left.bit
  right := frame.rightBit
  leftDistinct := frame.left.distinct
  rightDistinct := frame.rightDistinct
  cross := frame.cross
  controlLeft := frame.left.separate index
  controlRight := frame.rightControl index

/-- The paired stage contains exactly both old physical stage words in their original order. -/
lemma stage_source (frame : Frame encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stage : Fin controls × Nat) :
    (frame.pairFrame stage.1).serialGates
        (Permutation.transpositions (permutation ^ stage.2)) =
      frame.left.stageGates permutation stage ++
        frame.rightBarrel.stageGates permutation stage := rfl

def serialGates (frame : Frame encoding size controls)
    (permutation : Equiv.Perm (Fin size)) (stages : List (Fin controls × Nat)) :
    List (GateSpec encoding) :=
  frame.left.gates permutation stages ++ frame.rightBarrel.gates permutation stages

end Frame

end

end QuantumAlg.EncodedBit.PermutationBarrelParallel
