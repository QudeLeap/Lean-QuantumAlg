/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean.Support
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Factor

/-!
# Exact native lower uncomputation leaving only the high carry xor

The actual full clean-low word is followed by the reverse of its actual
lower clean-low word. Only the original low output is initialized; all
other carry outputs, including the high flag, remain arbitrary. This is a
reverse of native unitary gates, rather than of a measured instrument
[G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The actual native compute/uncompute pair changes exactly the original high output. -/
lemma cleanLowGates_uncompute_top {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) (state : Data)
    (clean : (layout.output ⟨0, by omega⟩).get state = false) :
    stepList (layout.lower.cleanLowGates (constant.setWidth length)).reverse
        (stepList (layout.cleanLowGates constant) state) =
      if layout.carryValues constant state (length + 1) then
        (layout.output (Fin.last length)).flip state else state := by
  have lowerClean : (layout.lower.output ⟨0, positive⟩).get state = false := clean
  have lowerEquation := cleanLowGates_step layout.lower (constant.setWidth length)
    state positive lowerClean
  have excluded (index : Fin length) :
      (layout.lower.output index).wire ≠ (layout.output (Fin.last length)).wire := by
    apply layout.output_ne
    intro equal
    have values := congrArg (fun value : Fin (length + 1) => value.val) equal
    change index.val = length at values
    have inside := index.isLt
    omega
  rw [cleanLowGates_step layout constant state (by omega) clean,
    gates_top_factor layout constant positive state, ← lowerEquation]
  by_cases carry : layout.carryValues constant state (length + 1)
  · rw [if_pos carry, if_pos carry,
      cleanLowGates_reverse_flip_comm layout.lower (constant.setWidth length)
        (layout.output (Fin.last length)) (layout.control_output_ne _)
        (fun index => layout.source_output_ne index.castSucc _) excluded,
      stepList_reverse_stepList]
  · rw [if_neg carry, if_neg carry, stepList_reverse_stepList]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
