/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Native

/-! # Actual geometry primitives exclude original work words and source flags -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit

/-- An original work-word or flag position lies outside every complete original metadata word. -/
def outsideMetadata (width : Nat) (observed : EncodedBit (SharedEEA.encoding width)) : Prop :=
  observed.wire.val < 2 * (width + 3) ∨
    2 * (width + 3) + 4 * width.size ≤ observed.wire.val

private lemma source_outside (width : Nat) (positive : 1 ≤ width) (field : Field)
    (observed : EncodedBit (SharedEEA.encoding width)) (outside : outsideMetadata width observed)
    (index : Fin (fullWidth width)) :
    ((source width positive field).bit index).wire ≠ (sourceBit width observed).wire := by
  unfold source
  dsimp only
  split
  · exact (source_prefix_ne width observed _).symm
  · intro same
    have values := congrArg Fin.val same
    rw [fieldBit_wire, sourceBit_wire] at values
    have within := index.isLt
    dsimp only [fullWidth, NumberTheory.SharedEEA.ScanMetadata.addressWidth] at within
    unfold outsideMetadata at outside
    cases field <;> simp only [fieldOffset] at values <;> omega

private lemma target_outside (width : Nat) (observed : EncodedBit (SharedEEA.encoding width))
    (index : Fin (fullWidth width)) :
    ((target width).bit index).wire ≠ (sourceBit width observed).wire := by
  unfold target
  dsimp only
  split
  · exact (source_conjunction_ne width observed).symm
  · exact (source_address_ne width observed _).symm

/-- Every actual native metadata adder or subtractor operand excludes an original work or flag. -/
lemma nativeFieldGates_bitDisjoint (width : Nat) (positive : 1 ≤ width) (field : Field)
    (subtract : Bool) (observed : EncodedBit (SharedEEA.encoding width))
    (outside : outsideMetadata width observed) (gate : GateSpec (encoding width))
    (present : gate ∈ nativeFieldGates width positive field subtract) :
    GateSpec.bitDisjoint (sourceBit width observed) gate := by
  have original : gate ∈ (placement width positive field).nativeGates := by
    cases subtract <;>
      simpa only [nativeFieldGates, Bool.false_eq_true, if_false, if_true, List.mem_reverse]
        using present
  exact (placement width positive field).nativeGates_bitDisjoint (sourceBit width observed)
    (source_outside width positive field observed outside) (target_outside width observed)
    gate original

/-- Actual constant instructions touch only the full temporary geometry target. -/
lemma nativeConstantGates_bitDisjoint (width : Nat) (constant : BitVec (fullWidth width))
    (observed : EncodedBit (SharedEEA.encoding width)) (gate : GateSpec (encoding width))
    (present : gate ∈ nativeConstantGates width constant) :
    GateSpec.bitDisjoint (sourceBit width observed) gate := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
  exact target_outside width observed index.rev

/-- Both actual coefficient words exclude all original word and source flag positions. -/
lemma nativeCoefficientGates_bitDisjoint (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (observed : EncodedBit (SharedEEA.encoding width)) (outside : outsideMetadata width observed)
    (gate : GateSpec (encoding width))
    (present : gate ∈ nativeCoefficientGates width positive deshift) :
    GateSpec.bitDisjoint (sourceBit width observed) gate := by
  rw [nativeCoefficientGates, List.mem_append] at present
  rcases present with constant | arithmetic
  · exact nativeConstantGates_bitDisjoint width _ observed gate constant
  · cases deshift with
    | false =>
        exact nativeFieldGates_bitDisjoint width positive .coefficient false
          observed outside gate arithmetic
    | true =>
        rcases List.mem_append.mp arithmetic with divisor | shift
        · exact nativeFieldGates_bitDisjoint width positive .divisor true
            observed outside gate divisor
        · exact nativeFieldGates_bitDisjoint width positive .shift true observed outside gate shift

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
