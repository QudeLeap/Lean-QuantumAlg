/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Prefix
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Preservation

/-! # Full physical pool and control preservation of the original signed native source word -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned

noncomputable section

open EncodedBit NumberTheory.SharedEEA ArithmeticTemplate

/-- Every source gate lies strictly before the original arbitrary Iter position. -/
lemma nativeWord_get_outside (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (observed : EncodedBit (encoding width))
    (outside : (SharedEEA.iterationBit width).wire.val ≤ observed.wire.val) (state : Data width) :
    observed.get (GateSpec.stepList (nativeWord width kind last) state) =
      observed.get state := by
  have operands : 2 * (width + 3) ≤ (SharedEEA.iterationBit width).wire.val := by
    rw [SharedEEA.iterationBit_wire]
    omega
  rw [nativeWord, GateSpec.stepList_append]
  have top := GateSpec.stepList_get_of_bitDisjoint (ArithmeticTop.source width kind last)
    observed (fun gate present => ArithmeticTemplate.below_disjoint gate
      (ArithmeticTop.source_below width kind last gate present) observed outside)
    (GateSpec.stepList (prefixGates width (stage kind) (last + 1)) state)
  exact top.trans (prefixGates_get_outside width (stage kind) (last + 1) observed
    (operands.trans outside) state)

/-- Signed overflow retains every original address, prefix and conjunction bit, even when dirty. -/
lemma nativeWord_pool (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (state : Data width) :
    (GateSpec.stepList (nativeWord width kind last) state).2 = state.2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : (SharedEEA.iterationBit width).wire.val ≤
        (addressBit width ⟨index, within⟩).wire.val := by
      rw [SharedEEA.iterationBit_wire, addressBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [addressBit_get] using
      nativeWord_get_outside width kind last (addressBit width ⟨index, within⟩) outside state
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : (SharedEEA.iterationBit width).wire.val ≤
        (prefixBit width ⟨index, within⟩).wire.val := by
      rw [SharedEEA.iterationBit_wire, prefixBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [prefixBit_get] using
      nativeWord_get_outside width kind last (prefixBit width ⟨index, within⟩) outside state
  · apply nativeWord_get_outside width kind last (conjunctionBit width)
    rw [SharedEEA.iterationBit_wire, conjunctionBit_wire, SharedEEA.encoding_width]
    omega

/-- The signed native source word retains the same original root control. -/
lemma nativeWord_control (width : Nat) (kind : ArithmeticTop.Kind) (last : Nat)
    (state : Data width) :
    (GateSpec.stepList (nativeWord width kind last) state).1.control = state.1.control := by
  apply nativeWord_get_outside width kind last (sourceBit width (SharedEEA.controlBit width))
  rw [SharedEEA.iterationBit_wire, sourceBit_wire, SharedEEA.controlBit_wire]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSigned
