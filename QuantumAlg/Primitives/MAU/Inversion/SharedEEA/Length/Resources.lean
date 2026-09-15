/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Refresh

/-!
# Actual native resources of the complete shared-EEA length refresh

Counts below follow the literal boundary, leading-position, and set-bit
enumerations. Every predicate includes its negative masks and arbitrary
Iter cleanup. A nonmatching predicate remains part of the emitted circuit.
The four serial writes occur in the source order
[LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341].

These are bounds for this implemented finite selection construction; they
are not the paper's asymptotic constants. Its key count is at most twice
the original word parameter plus two, and the remaining enumerations are
over actual word positions and existing length bits. The complete program
uses the same original register encoding and introduces no workspace field.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthResources

noncomputable section

open EncodedBit LengthCoordinates

private theorem flatMap_length_le {Source Target : Type} (items : List Source)
    (emit : Source → List Target) (bound : Nat)
    (bounded : ∀ item ∈ items, (emit item).length ≤ bound) :
    (items.flatMap emit).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons head rest ih =>
      have current := bounded head List.mem_cons_self
      have tailBound := ih (fun item present => bounded item (List.mem_cons_of_mem head present))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      omega

/-- Every real leading predicate fits the physical source-key and full-word envelope. -/
theorem predicate_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) (output : Fin width.size) :
    (LengthPredicate.gates width field key firstWord position output).length ≤
      10 * (width.size + (width + 3)) + 1 := by
  have actual := LengthPredicate.gates_length_le width field key firstWord position output
  have within := position.isLt
  have regionBound := region_le width field key
  omega

/-- A candidate calls the actual predicate at most once for each existing target length bit. -/
theorem position_length_le (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (position : Fin (region width field key)) :
    (LengthWrite.positionGates width field key firstWord position).length ≤
      width.size * (10 * (width.size + (width + 3)) + 1) := by
  unfold LengthWrite.positionGates
  calc
    _ ≤ (Word.constantOneIndices (LengthWrite.positionConstant width field key position)).length *
        (10 * (width.size + (width + 3)) + 1) :=
      flatMap_length_le _ _ _ (fun output _ =>
        predicate_length_le width field key firstWord position output)
    _ ≤ _ := Nat.mul_le_mul_right _ (Word.constantOneIndices_length_le _)

/-- Each retained-key call visits every physical leading position, including inactive ones. -/
theorem key_length_le (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool) :
    (LengthWrite.gates width field key firstWord).length ≤
      (width + 3) * (width.size * (10 * (width.size + (width + 3)) + 1)) := by
  unfold LengthWrite.gates
  calc
    _ ≤ (List.ofFn (fun position : Fin (region width field key) => position)).length *
        (width.size * (10 * (width.size + (width + 3)) + 1)) :=
      flatMap_length_le _ _ _ (fun position _ =>
        position_length_le width field key firstWord position)
    _ = region width field key *
        (width.size * (10 * (width.size + (width + 3)) + 1)) := by
      rw [List.length_ofFn]
    _ ≤ _ := Nat.mul_le_mul_right _ (region_le width field key)

/-- One actual dynamic-boundary write includes every finite key's complete native list. -/
theorem schedule_length_le (width : Nat) (field : Field) (firstWord : Bool) :
    (LengthSchedule.gates width field firstWord).length ≤
      2 ^ width.size * ((width + 3) *
        (width.size * (10 * (width.size + (width + 3)) + 1))) := by
  unfold LengthSchedule.gates
  calc
    _ ≤ (LengthSchedule.keys width).length * ((width + 3) *
        (width.size * (10 * (width.size + (width + 3)) + 1))) :=
      flatMap_length_le _ _ _ (fun key _ => key_length_le width field key firstWord)
    _ = _ := by rw [LengthSchedule.keys_length]

/-- The source's finite length-key count grows at most linearly, including parameter zero. -/
theorem key_count_le (width : Nat) : 2 ^ width.size ≤ 2 * (width + 1) := by
  by_cases zero : width = 0
  · subst width
    decide
  · have positive : 0 < width := by omega
    have lengthPositive := Nat.size_pos.mpr positive
    have lower : 2 ^ (width.size - 1) ≤ width := Nat.lt_size.mp (by omega)
    have exponent : width.size - 1 + 1 = width.size := by omega
    have doubled : 2 ^ width.size = 2 ^ (width.size - 1) * 2 := by
      calc
        _ = 2 ^ (width.size - 1 + 1) := congrArg (fun power => 2 ^ power) exponent.symm
        _ = _ := Nat.pow_succ _ _
    rw [doubled]
    omega

/-- The four actual writes are all charged, including the two old-length cleanup writes. -/
theorem refresh_length_le (width : Nat) :
    (LengthRefresh.gates width).length ≤
      4 * (2 ^ width.size * ((width + 3) *
        (width.size * (10 * (width.size + (width + 3)) + 1)))) := by
  have oldCoefficient := schedule_length_le width .coefficient false
  have newCoefficient := schedule_length_le width .coefficient true
  have oldDivisor := schedule_length_le width .divisor true
  have newDivisor := schedule_length_le width .divisor false
  simp only [LengthRefresh.gates, List.length_append]
  omega

/-- Eliminating the key power gives an explicit polynomial enumeration envelope. -/
theorem refresh_length_le_polynomial (width : Nat) :
    (LengthRefresh.gates width).length ≤
      4 * ((2 * (width + 1)) * ((width + 3) *
        (width * (10 * (width + (width + 3)) + 1)))) := by
  have lengthBound : width.size ≤ width := Nat.size_le.mpr Nat.lt_two_pow_self
  have predicateBound : 10 * (width.size + (width + 3)) + 1 ≤
      10 * (width + (width + 3)) + 1 := by omega
  have targetBound := Nat.mul_le_mul lengthBound predicateBound
  exact (refresh_length_le width).trans
    (Nat.mul_le_mul_left 4 (Nat.mul_le_mul (key_count_le width)
      (Nat.mul_le_mul_left (width + 3) targetBound)))

/-- Every actual native event is retained in the full program's trace count. -/
theorem refresh_eventTrace_length (width : Nat) :
    (LengthRefresh.program width).eventTrace.length = (LengthRefresh.gates width).length := by
  rw [LengthRefresh.program_eventTrace, List.length_map]

/-- Strict unit-event depth counts the complete actual sequential elementary list. -/
theorem refresh_unitDepth (width : Nat) :
    (LengthRefresh.program width).evaluatedEventDepth (fun _ => 1) =
      (LengthRefresh.gates width).length :=
  GateSpec.programList_evaluatedEventDepth_unit _

/-- The literal inverse restores all fields and has exactly the same actual elementary count. -/
theorem refresh_reverse_length (width : Nat) :
    (LengthRefresh.gates width).reverse.length = (LengthRefresh.gates width).length :=
  List.length_reverse

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthResources
