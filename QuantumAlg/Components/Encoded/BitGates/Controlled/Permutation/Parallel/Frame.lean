/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Preservation
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin.Parallel.Correctness
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin.Parallel.Resources

/-! # Two complete physical permutation words with one retained quantum control -/

namespace QuantumAlg.EncodedBit.PermutationParallel

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- The two complete words are mutually disjoint and outside their common actual control. -/
structure Frame (encoding : BinaryLabelEncoding Data) (size : Nat) where
  control : EncodedBit encoding
  left : Fin size → EncodedBit encoding
  right : Fin size → EncodedBit encoding
  leftDistinct : Function.Injective (fun index => (left index).wire)
  rightDistinct : Function.Injective (fun index => (right index).wire)
  cross : ∀ first second, (left first).wire ≠ (right second).wire
  controlLeft : ∀ index, control.wire ≠ (left index).wire
  controlRight : ∀ index, control.wire ≠ (right index).wire

namespace Frame

def leftFrame (frame : Frame encoding size) : PermutationFrame encoding size where
  control := frame.control
  bit := frame.left
  distinct := frame.leftDistinct
  separate := frame.controlLeft

def rightFrame (frame : Frame encoding size) : PermutationFrame encoding size where
  control := frame.control
  bit := frame.right
  distinct := frame.rightDistinct
  separate := frame.controlRight

/-- Each actual exchange supplies exactly five distinct original physical positions. -/
def exchangeFrame (frame : Frame encoding size)
    (exchange : Permutation.Transposition (Fin size)) : FredkinParallel.Frame encoding where
  bit := ![frame.control, frame.left exchange.first, frame.left exchange.second,
    frame.right exchange.first, frame.right exchange.second]
  distinct := by
    have cl := frame.controlLeft exchange.first
    have cr := frame.controlLeft exchange.second
    have dl := frame.controlRight exchange.first
    have dr := frame.controlRight exchange.second
    have left := frame.leftDistinct.ne exchange.different
    have right := frame.rightDistinct.ne exchange.different
    have ll := frame.cross exchange.first exchange.first
    have lr := frame.cross exchange.first exchange.second
    have rl := frame.cross exchange.second exchange.first
    have rr := frame.cross exchange.second exchange.second
    intro first second same
    fin_cases first <;> fin_cases second <;> simp_all

/-- The retained original source runs the complete first word before the complete second word. -/
def serialGates (frame : Frame encoding size)
    (exchanges : List (Permutation.Transposition (Fin size))) : List (GateSpec encoding) :=
  frame.leftFrame.gates exchanges ++ frame.rightFrame.gates exchanges

/-- The five-wire helper contains exactly the same original pair of singleton source words. -/
lemma exchangeFrame_serialGates (frame : Frame encoding size)
    (exchange : Permutation.Transposition (Fin size)) :
    (frame.exchangeFrame exchange).serialGates =
      frame.leftFrame.gates [exchange] ++ frame.rightFrame.gates [exchange] := rfl

end Frame

end

end QuantumAlg.EncodedBit.PermutationParallel
