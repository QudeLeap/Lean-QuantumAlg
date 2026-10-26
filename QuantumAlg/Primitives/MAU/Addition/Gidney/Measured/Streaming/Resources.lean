/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Rows
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Gates

/-!
# Exact literal native Toffoli multiplicity of the chronological measured stream

Every non-low carry row has one actual addressed Toffoli. The low static
offset bit selects whether the zero-input carry row contains one. Physical
vents and extraction/finish CNOTs introduce no Toffoli. These are counts of
the actual source-order instruction generator [G25, main.tex:199-251].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private lemma offsetGates_toffoli (layout : Layout encoding width) (constant : BitVec width) :
    ((layout.offsetGates constant).map toffoliMultiplicity).sum = 0 := by
  apply List.sum_eq_zero
  intro amount member
  obtain ⟨gate, present, rfl⟩ := List.mem_map.mp member
  unfold offsetGates at present
  obtain ⟨row, listed, inside⟩ := List.mem_flatten.mp present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp listed
  cases chosen : constant.getLsbD index.val with
  | false => simp only [chosen, Bool.false_eq_true, if_false, List.not_mem_nil] at inside
  | true =>
      simp only [chosen, if_true, List.mem_singleton] at inside
      subst gate
      rfl

private lemma extractCarryGates_toffoli (layout : Layout encoding width)
    (index : Fin (width - 1)) :
    ((layout.extractCarryGates index).map toffoliMultiplicity).sum = 0 := by
  unfold extractCarryGates
  split_ifs <;> rfl

private lemma finishCarryGates_toffoli (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    ((layout.finishCarryGates wide constant index).map toffoliMultiplicity).sum = 0 := by
  unfold finishCarryGates
  split_ifs <;> rfl

private lemma computeCarryGates_toffoli (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    ((layout.computeCarryGates wide constant index).map toffoliMultiplicity).sum =
      if index.val = 0 then (constant.getLsbD index.val).toNat else 1 := by
  unfold computeCarryGates
  by_cases first : index.val = 0
  · rw [if_pos first, if_pos first]
    cases constant.getLsbD index.val <;> rfl
  · rw [if_neg first, if_neg first]
    apply affineToffoliGates_toffoliMultiplicity

/-- The literal measured row pays one Toffoli except for the statically simplified low row. -/
lemma streamingStep_toffoliCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (index : Fin (width - 1)) :
    wordToffoliCount (layout.streamingStep wide constant index) =
      if index.val = 0 then (constant.getLsbD index.val).toNat else 1 := by
  unfold streamingStep
  rw [wordToffoliCount_append, wordToffoliCount_append]
  have ventZero : wordToffoliCount (encoding := encoding) (records := width - 2)
      (if positive : 0 < index.val then
        [.vent (layout.carryHelper index.val) ⟨index.val - 1, by omega⟩] else []) = 0 := by
    split_ifs <;> rfl
  rw [ventZero]
  simp only [wordToffoliCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    toffoliCount, computeCarryGates_toffoli, extractCarryGates_toffoli,
    finishCarryGates_toffoli, Nat.add_zero]

/-- The literal increasing-index source prefix has exactly its native Toffoli multiplicity. -/
lemma streamingRows_toffoliCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (count : Nat) (bounded : count ≤ width - 1) :
    wordToffoliCount (layout.streamingRows wide constant count bounded) =
      count - 1 + if 0 < count then (constant.getLsbD 0).toNat else 0 := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows, wordToffoliCount_append, ih (by omega), streamingStep_toffoliCount]
      cases count with
      | zero => rfl
      | succ count =>
          have positive : 0 < count + 1 := by omega
          have different : count + 1 ≠ 0 := by omega
          rw [if_pos positive, if_neg different, if_pos (by omega : 0 < count + 1 + 1)]
          omega

/-- The complete measured stream has width-minus-two fixed Toffolis plus its static low bit. -/
lemma streamingWord_toffoliCount (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) :
    wordToffoliCount (layout.streamingWord wide constant) =
      width - 2 + (constant.getLsbD 0).toNat := by
  rw [streamingWord_eq_rows]
  change ((layout.offsetGates constant).map toffoliMultiplicity).sum +
    wordToffoliCount (layout.streamingRows wide constant (width - 1) le_rfl) = _
  rw [offsetGates_toffoli, Nat.zero_add, streamingRows_toffoliCount,
    if_pos (by omega : 0 < width - 1)]
  congr 1

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
