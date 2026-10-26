/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.NativeFold

/-! # Full physical complement of the native streamed source prefix -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Every native source-prefix gate remains inside the two original work words. -/
lemma prefixGates_get_outside (width : Nat) (stage : Stage) (count : Nat)
    (observed : EncodedBit (encoding width)) (outside : 2 * (width + 3) ≤ observed.wire.val)
    (state : Data width) :
    observed.get (GateSpec.stepList (prefixGates width stage count) state) =
      observed.get state := by
  apply GateSpec.stepList_get_of_bitDisjoint
  intro gate present
  obtain ⟨index, _, present⟩ := List.mem_flatMap.mp present
  exact below_disjoint gate (source_below width stage index gate present) observed outside

/-- Reversing the same literal source gates retains their complete original complement. -/
lemma prefixGates_reverse_get_outside (width : Nat) (stage : Stage) (count : Nat)
    (observed : EncodedBit (encoding width)) (outside : 2 * (width + 3) ≤ observed.wire.val)
    (state : Data width) :
    observed.get (GateSpec.stepList (prefixGates width stage count).reverse state) =
      observed.get state := by
  apply GateSpec.stepList_get_of_bitDisjoint
  intro gate present
  obtain ⟨index, _, present⟩ := List.mem_flatMap.mp (List.mem_reverse.mp present)
  exact below_disjoint gate (source_below width stage index gate present) observed outside

/-- All actual address bits remain unchanged by the source prefix. -/
lemma prefixGates_address (width : Nat) (stage : Stage) (count : Nat) (state : Data width) :
    (GateSpec.stepList (prefixGates width stage count) state).2.1 = state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have outside : 2 * (width + 3) ≤ (addressBit width ⟨index, within⟩).wire.val := by
    rw [addressBit_wire, SharedEEA.encoding_width]
    omega
  simpa only [addressBit_get] using
    prefixGates_get_outside width stage count (addressBit width ⟨index, within⟩) outside state

/-- Every physical pool position is retained, including an arbitrary incoming conjunction. -/
lemma prefixGates_pool (width : Nat) (stage : Stage) (count : Nat) (state : Data width) :
    (GateSpec.stepList (prefixGates width stage count) state).2 = state.2 := by
  refine Prod.ext (prefixGates_address width stage count state) (Prod.ext ?_ ?_)
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    have outside : 2 * (width + 3) ≤ (prefixBit width ⟨index, within⟩).wire.val := by
      rw [prefixBit_wire, SharedEEA.encoding_width]
      omega
    simpa only [prefixBit_get] using
      prefixGates_get_outside width stage count (prefixBit width ⟨index, within⟩) outside state
  · apply prefixGates_get_outside width stage count (conjunctionBit width)
    rw [conjunctionBit_wire, SharedEEA.encoding_width]
    omega

/-- The actual original root control is retained by all native source-prefix instructions. -/
lemma prefixGates_control (width : Nat) (stage : Stage) (count : Nat) (state : Data width) :
    (GateSpec.stepList (prefixGates width stage count) state).1.control = state.1.control := by
  apply prefixGates_get_outside width stage count (sourceBit width (SharedEEA.controlBit width))
  rw [sourceBit_wire, SharedEEA.controlBit_wire]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTemplate
