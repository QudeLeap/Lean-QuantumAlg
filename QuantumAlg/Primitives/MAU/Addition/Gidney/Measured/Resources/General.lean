/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Toffoli
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Resources.Coordinates

/-!
# Native measured-adder bounds including the separate two-bit source word

The two-bit circuit retains its one static low carry and no dirty-carry
repair. Larger words use the existing literal source recurrences. These
are native counts of the same chronological program, independently of the
modulus parity [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The two-bit native repair has no Toffoli: its original dirty word is empty. -/
lemma tailWord_toffoli_width_two (layout : Layout encoding 2) (constant : BitVec 2) :
    wordToffoliCount (layout.tailWord constant) = 0 := by
  simp only [tailWord, wordToffoliCount_append, phaseWord_toffoliCount,
    native_singleton_toffoli, complementGates_toffoli, Nat.zero_add, Nat.add_zero]
  rfl

/-- The literal two-bit measured adder pays exactly its selected low-carry Toffoli. -/
lemma adderWord_toffoli_width_two (layout : Layout encoding 2) (constant : BitVec 2) :
    wordToffoliCount (layout.adderWord (by decide) constant) =
      (constant.getLsbD 0).toNat := by
  rw [adderWord_eq_stream_tail, wordToffoliCount_append, streamingWord_toffoliCount,
    tailWord_toffoli_width_two]
  omega

/-- Every admitted width retains its independently counted native carry allowance. -/
lemma adderWord_toffoli_bound_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    wordToffoliCount (layout.adderWord wide constant) ≤
      if width = 2 then 1 else 3 * width - 6 := by
  have low : (constant.getLsbD 0).toNat ≤ 1 := by
    cases constant.getLsbD 0 <;> decide
  by_cases two : width = 2
  · subst width
    rw [if_pos rfl, adderWord_toffoli_width_two]
    exact low
  · rw [if_neg two, adderWord_toffoliCount layout wide (by omega)]
    omega

/-- The separate two-bit CNOT allowance and the larger-word recurrence count the actual word. -/
lemma adderWord_cnot_bound_general (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    wordCnotCount (layout.adderWord wide constant) ≤
      if width = 2 then 3 else 13 * width - 27 := by
  by_cases two : width = 2
  · subst width
    rw [if_pos rfl, adderWord_eq_stream_tail]
    simp only [tailWord, wordCnotCount_append, native_cnot, complement_cnot,
      phase_cnot, Nat.zero_add, Nat.add_zero]
    have stream := streamingWord_cnot_bound layout wide constant
    have empty : ((layout.carryLayout.gates (constant.setWidth (2 - 2))).map
        cnotMultiplicity).sum = 0 := rfl
    rw [empty]
    exact stream
  · rw [if_neg two]
    exact adderWord_cnot_bound layout wide (by omega) constant

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
