/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Frame

/-! # Exact complete readouts of the actual terminal boundary subtraction -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The padded source includes the original actual conjunction, without a clean premise. -/
def sourceValue (width : Nat) (field : Field) (state : Data width) :
    BitVec (ScanMetadata.addressWidth width) :=
  BitVec.cons state.2.2.2 (boundaryValue field state.1)

/-- Every source coordinate has the declared complete finite value. -/
lemma source_get (width : Nat) (field : Field) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    ((source width field).bit index).get state =
      (sourceValue width field state).getMsbD index.val := by
  unfold source
  dsimp only
  split
  · rename_i zero
    rw [sourceValue, zero, BitVec.getMsbD_cons_zero]
    rfl
  · rename_i nonzero
    rw [sourceBit_get, boundaryBit_get]
    have successor : index.val = (index.val - 1) + 1 := by omega
    unfold sourceValue
    conv_rhs => rw [successor, BitVec.getMsbD_cons_succ]

/-- The target is the whole actual prefix, with no dropped high or padding position. -/
lemma target_get (width : Nat) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    ((target width).bit index).get state = state.2.2.1.getMsbD index.val :=
  prefixBit_get width index state

/-- Actual inverse addition gives the complete modular boundary difference in the prefix. -/
lemma subtractStep_prefix (width : Nat) (field : Field) (state : Data width) :
    ((placement width field).subtractStep state).2.2.1 =
      state.2.2.1 - sourceValue width field state := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have actual := (placement width field).subtractStep_target_get state
    (sourceValue width field state) state.2.2.1 (source_get width field state)
    (target_get width state) ⟨index, within⟩
  change (prefixBit width ⟨index, within⟩).get _ = _ at actual
  simpa only [prefixBit_get] using actual

/-- Every original physical source bit survives, including both length fields and dirty Iter. -/
lemma subtractStep_original (width : Nat) (field : Field) (state : Data width)
    (observed : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width observed).get ((placement width field).subtractStep state) =
      (sourceBit width observed).get state :=
  (placement width field).subtractStep_get_of_target_ne state _
    (fun index => (source_prefix_ne width observed index).symm)

/-- The same actual padding bit is restored even though it participates in the real arithmetic. -/
lemma subtractStep_conjunction (width : Nat) (field : Field) (state : Data width) :
    ((placement width field).subtractStep state).2.2.2 = state.2.2.2 :=
  (placement width field).subtractStep_get_of_target_ne state _
    (fun index => prefix_conjunction_ne width index)

/-- The complete address is outside this real prefix arithmetic and remains arbitrary. -/
lemma subtractStep_address (width : Nat) (field : Field) (state : Data width) :
    ((placement width field).subtractStep state).2.1 = state.2.1 := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  simpa only [addressBit_get] using
    (placement width field).subtractStep_get_of_target_ne state
      (addressBit width ⟨index, within⟩)
      (fun other => (address_prefix_ne width ⟨index, within⟩ other).symm)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
