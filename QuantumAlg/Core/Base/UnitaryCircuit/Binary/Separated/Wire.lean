/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module


public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Separated
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Wire
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Separated
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Wire

/-!
# Relating one-wire and separated-wire raw-vector layouts

The two placement APIs use different tensor brackets around the same ordered
physical factors.  This module exposes their exact width-transport bridge.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

/-- Viewing the first active wire of a separated layout as a one-wire layout
only rebrackets its untouched suffix. -/
public theorem binaryWireVec_eq_binarySeparatedVec {width : Nat}
    (left right : Fin width) (before : left.val < right.val)
    (prefixState : HilbertVector (Qubits left.val))
    (first : HilbertVector (Qubits 1))
    (middle : HilbertVector (Qubits (right.val - left.val - 1)))
    (second : HilbertVector (Qubits 1))
    (suffix : HilbertVector (Qubits (width - right.val - 1))) :
    binaryWireVec left prefixState first
        (castQubitWidthVec (by omega :
          (right.val - left.val - 1) + (1 + (width - right.val - 1)) =
            width - left.val - 1)
          (HilbertVector.tensor middle
            (HilbertVector.tensor second suffix))) =
      binarySeparatedVec left right before prefixState
        (HilbertVector.tensor first second) middle suffix := by
  let tail := HilbertVector.tensor middle
    (HilbertVector.tensor second suffix)
  have tailWidth :
      (right.val - left.val - 1) + (1 + (width - right.val - 1)) =
        width - left.val - 1 := by omega
  have wireSourceWidth :
      (left.val + 1) +
          ((right.val - left.val - 1) + (1 + (width - right.val - 1))) =
        width := by omega
  have canonicalWidth :
      left.val +
          (1 + ((right.val - left.val - 1) +
            (1 + (width - right.val - 1)))) = width := by omega
  have separatedWidth :
      (left.val + ((1 + (right.val - left.val - 1)) + 1)) +
          (width - right.val - 1) = width := by omega
  have separatedToCanonical :
      (left.val + ((1 + (right.val - left.val - 1)) + 1)) +
          (width - right.val - 1) =
        left.val +
          (1 + ((right.val - left.val - 1) +
            (1 + (width - right.val - 1)))) := by omega
  unfold binaryWireVec
  change castQubitWidthVec _
      (HilbertVector.tensor (HilbertVector.tensor prefixState first)
        (castQubitWidthVec tailWidth tail)) = _
  calc
    castQubitWidthVec _
        (HilbertVector.tensor (HilbertVector.tensor prefixState first)
          (castQubitWidthVec tailWidth tail)) =
        castQubitWidthVec wireSourceWidth
          (HilbertVector.tensor (HilbertVector.tensor prefixState first) tail) := by
            simpa using
              (castQubitWidthVec_tensor_right tailWidth
                (by omega : (left.val + 1) + (width - left.val - 1) = width)
                (HilbertVector.tensor prefixState first) tail)
    _ = castQubitWidthVec canonicalWidth
          (HilbertVector.tensor prefixState
            (HilbertVector.tensor first tail)) := by
          calc
            castQubitWidthVec wireSourceWidth
                (HilbertVector.tensor (HilbertVector.tensor prefixState first) tail) =
              castQubitWidthVec canonicalWidth
                (castQubitWidthVec (by omega :
                    (left.val + 1) +
                        ((right.val - left.val - 1) +
                        (1 + (width - right.val - 1))) =
                      left.val +
                        (1 + ((right.val - left.val - 1) +
                          (1 + (width - right.val - 1)))))
                  (HilbertVector.tensor
                    (HilbertVector.tensor prefixState first) tail)) := by
                      rw [castQubitWidthVec_trans]
            _ = _ := by
              rw [castQubitWidthVec_tensor_assoc]
    _ = castQubitWidthVec canonicalWidth
          (castQubitWidthVec separatedToCanonical
            (HilbertVector.tensor
              (HilbertVector.tensor prefixState
                (HilbertVector.tensor
                  (HilbertVector.tensor first middle) second)) suffix)) := by
          congr 1
          simpa [tail] using
            (castQubitWidthVec_tensor_right_to_separated5
              prefixState first middle second suffix)
    _ = castQubitWidthVec separatedWidth
          (HilbertVector.tensor
            (HilbertVector.tensor prefixState
              (HilbertVector.tensor
                (HilbertVector.tensor first middle) second)) suffix) := by
          rw [castQubitWidthVec_trans]
    _ = binarySeparatedVec left right before prefixState
          (HilbertVector.tensor first second) middle suffix := by
          exact (binarySeparatedVec_tensor left right before prefixState
            first second middle suffix).symm

end

end QuantumAlg.UnitaryCircuit
