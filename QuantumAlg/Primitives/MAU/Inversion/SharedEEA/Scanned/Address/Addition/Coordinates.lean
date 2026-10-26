/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Addition

/-! # Exact input and output bit reads of the placed full-carry addition -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition

noncomputable section

open EncodedBit BinaryLabelEncoding NumberTheory.SharedEEA

private def firstLens (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    EncodedBit (Addition.TTK.encoding (ScanMetadata.addressWidth width)) :=
  prodLeftBit (finIdentity _) (finIdentity _) (finIdentityBit _ index)

private def secondLens (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    EncodedBit (Addition.TTK.encoding (ScanMetadata.addressWidth width)) :=
  prodRightBit (finIdentity _) (finIdentity _) (finIdentityBit _ index)

private lemma first_location (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (placement width).wires (firstLens width index).wire = ((source width).bit index).wire :=
  wordPairSubsystem_left _ _ _ _ _ index

private lemma second_location (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (placement width).wires (secondLens width index).wire =
      ((AddressCopy.target width).bit index).wire :=
  wordPairSubsystem_right _ _ _ _ _ index

/-- The first grouped operand is read at the literal quotient/padding positions. -/
lemma grouped_source_get (width : Nat) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    (firstLens width index).get
      (((placement width).full (source_total width) (encoding_surjective width)).grouping state).1 =
      ((source width).bit index).get state :=
  (placement width).full_source_read (source_total width) (encoding_surjective width)
    (firstLens width index) ((source width).bit index) (first_location width index) state

/-- The second grouped operand is the complete address, including its carry bit. -/
lemma grouped_target_get (width : Nat) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    (secondLens width index).get
      (((placement width).full (source_total width) (encoding_surjective width)).grouping state).1 =
      (addressBit width index).get state :=
  (placement width).full_source_read (source_total width) (encoding_surjective width)
    (secondLens width index) (addressBit width index) (second_location width index) state

/-- Every source quotient bit and the high padding bit survive the actual native addition. -/
lemma step_source_get (width : Nat) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    ((source width).bit index).get (step width state) = ((source width).bit index).get state := by
  have after := (placement width).full_step_source_read (source_total width)
    (encoding_surjective width) (firstLens width index) ((source width).bit index)
    (first_location width index) Addition.TTK.lowOutput state
  exact after.trans (grouped_source_get width state index)

/-- All original fields outside the two actual operand words retain every bit. -/
lemma step_other_get (width : Nat) (state : Data width) (bit : EncodedBit (encoding width))
    (outside : bit.wire ∉ Set.range (placement width).wires) :
    bit.get (step width state) = bit.get state :=
  (placement width).full_step_other_read (source_total width) (encoding_surjective width)
    bit outside Addition.TTK.lowOutput state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition
