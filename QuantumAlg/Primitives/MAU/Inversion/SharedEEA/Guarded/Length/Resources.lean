/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Length.Refresh
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Resources

/-!
# Actual resources of the enlarged-source guarded length refresh

Every native leading predicate now reads all three retained length fields:
quotient, low shift, and the selected other length. Counts retain all actual
guard controls and dirty-work cleanup. The same four source-ordered writes
are all present in the emitted circuit
[LYL+26, sec_EEA/sub_regshare.tex:309-313;
sec_circuit/sub_block_new.tex:211-219,338-341].

The explicit bounds belong to this actual finite enumeration construction.
No nonmatching guard or retained-key call is removed from the event count.
The original register encoding, including arbitrary original Iter, is the
complete carrier; no workspace field is added by this construction.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthResources

noncomputable section

open EncodedBit LengthCoordinates

private lemma predicate_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (output : Fin width.size) :
    (GuardedLengthPredicate.gates width field key firstWord position output).length ≤
      10 * (3 * width.size + (width + 3)) + 1 := by
  have actual := GuardedLengthPredicate.gates_length_le width field key firstWord position output
  have within := position.isLt
  have regionBound := region_le width field key
  omega

private lemma position_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) :
    (GuardedLengthWrite.positionGates width field key firstWord position).length ≤
      width.size * (10 * (3 * width.size + (width + 3)) + 1) := by
  unfold GuardedLengthWrite.positionGates
  calc
    _ ≤ (Word.constantOneIndices (LengthWrite.positionConstant width field key position)).length *
        (10 * (3 * width.size + (width + 3)) + 1) :=
      LengthResources.flatMap_length_le _ _ _ (fun output _ =>
        predicate_length_le width field key firstWord position output)
    _ ≤ _ := Nat.mul_le_mul_right _ (Word.constantOneIndices_length_le _)

private lemma key_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) :
    (GuardedLengthWrite.keyGates width field key firstWord).length ≤
      (width + 3) * (width.size * (10 * (3 * width.size + (width + 3)) + 1)) := by
  unfold GuardedLengthWrite.keyGates
  calc
    _ ≤ (List.ofFn (fun position : Fin (region width field key) => position)).length *
        (width.size * (10 * (3 * width.size + (width + 3)) + 1)) :=
      LengthResources.flatMap_length_le _ _ _ (fun position _ =>
        position_length_le width field key firstWord position)
    _ = region width field key *
        (width.size * (10 * (3 * width.size + (width + 3)) + 1)) := by
      rw [List.length_ofFn]
    _ ≤ _ := Nat.mul_le_mul_right _ (region_le width field key)

/-- Every actual boundary call is charged with its enlarged source prefix and complete cleanup. -/
lemma schedule_length_le (width : Nat) (field : Field) (firstWord : Bool) :
    (GuardedLengthWrite.gates width field firstWord).length ≤
      2 ^ width.size * ((width + 3) *
        (width.size * (10 * (3 * width.size + (width + 3)) + 1))) := by
  unfold GuardedLengthWrite.gates
  calc
    _ ≤ (LengthSchedule.keys width).length * ((width + 3) *
        (width.size * (10 * (3 * width.size + (width + 3)) + 1))) :=
      LengthResources.flatMap_length_le _ _ _ (fun key _ =>
        key_length_le width field key firstWord)
    _ = _ := by rw [LengthSchedule.keys_length]

/-- All four actual guarded source-ordered writes contribute their entire native event lists. -/
lemma refresh_length_le (width : Nat) :
    (GuardedLengthRefresh.gates width).length ≤
      4 * (2 ^ width.size * ((width + 3) *
        (width.size * (10 * (3 * width.size + (width + 3)) + 1)))) := by
  unfold GuardedLengthRefresh.gates
  have actual := LengthResources.flatMap_length_le GuardedLengthRefresh.blocks
    (fun block => GuardedLengthWrite.gates width block.1 block.2) _
    (fun block _ => schedule_length_le width block.1 block.2)
  exact actual

/-- Eliminating all finite-key and bit-length growth gives a literal polynomial upper bound. -/
lemma refresh_length_le_polynomial (width : Nat) :
    (GuardedLengthRefresh.gates width).length ≤
      4 * ((2 * (width + 1)) * ((width + 3) *
        (width * (10 * (3 * width + (width + 3)) + 1)))) := by
  have lengthBound : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  have predicateBound : 10 * (3 * width.size + (width + 3)) + 1 ≤
      10 * (3 * width + (width + 3)) + 1 := by omega
  have targetBound := Nat.mul_le_mul lengthBound predicateBound
  exact (refresh_length_le width).trans
    (Nat.mul_le_mul_left 4 (Nat.mul_le_mul (LengthResources.key_count_le width)
      (Nat.mul_le_mul_left (width + 3) targetBound)))

/-- The actual ordered trace has exactly the full number of emitted elementary gates. -/
lemma refresh_eventTrace_length (width : Nat) :
    (GuardedLengthRefresh.program width).eventTrace.length =
      (GuardedLengthRefresh.gates width).length := by
  rw [GuardedLengthRefresh.program_eventTrace, List.length_map]

/-- Strict actual depth includes every retained-key, leading-position, and set-bit call. -/
lemma refresh_unitDepth (width : Nat) :
    (GuardedLengthRefresh.program width).evaluatedEventDepth (fun _ => 1) =
      (GuardedLengthRefresh.gates width).length :=
  GateSpec.programList_evaluatedEventDepth_unit _ .empty _

/-- Every elementary cleanup gate remains in the actual inverse count. -/
lemma refresh_reverse_length (width : Nat) :
    (GuardedLengthRefresh.gates width).reverse.length = (GuardedLengthRefresh.gates width).length :=
  List.length_reverse

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthResources
