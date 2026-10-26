/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates
import Mathlib.Data.Sum.Basic

/-!
# Existing output flags beside an actual physical subsystem

A distinct existing flag position extends the declared source subsystem.
The surrounding physical register is unchanged and no system is
allocated. Native operand bits keep their exact original addresses.
-/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target} (placement : WireSubsystem source target)

/-- Include one distinct existing output bit while retaining the complete physical frame. -/
def withFlag (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire) :
    WireSubsystem (.prod source .bool) target where
  wires :=
    { toFun := fun index => Sum.elim placement.wires (fun _index : Fin 1 => flag.wire)
        (finSumFinEquiv.symm index)
      inj' := (placement.wires.injective.sumElim
        (fun _left _right _same => Subsingleton.elim _ _)
        (fun index _flag => separate index)).comp finSumFinEquiv.symm.injective }

/-- Every original source position stays at its same declared actual wire. -/
lemma withFlag_source (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire) (index : Fin source.width) :
    (placement.withFlag flag separate).wires (Fin.castAdd 1 index) = placement.wires index := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.castAdd 1 index)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- The output flag names the actual existing target position. -/
lemma withFlag_flag (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire) :
    (placement.withFlag flag separate).wires (Fin.natAdd source.width (0 : Fin 1)) =
      flag.wire := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.natAdd source.width (0 : Fin 1))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Placing a native original operand lens beside the flag keeps its complete encoded-bit action. -/
lemma withFlag_place_source (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire)
    (sourceOnto : Function.Surjective source.encode)
    (combinedOnto : Function.Surjective (BinaryLabelEncoding.prod source .bool).encode)
    (targetOnto : Function.Surjective target.encode) (bit : EncodedBit source) :
    (placement.withFlag flag separate).placeBit combinedOnto targetOnto
      (BinaryLabelEncoding.prodLeftBit source .bool bit) =
      placement.placeBit sourceOnto targetOnto bit := by
  apply EncodedBit.eq_of_wire_eq
  rw [placeBit_wire, placeBit_wire]
  exact placement.withFlag_source flag separate bit.wire

/-- The source overflow lens places to exactly the caller's existing arbitrary flag. -/
lemma withFlag_place_flag (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire)
    (combinedOnto : Function.Surjective (BinaryLabelEncoding.prod source .bool).encode)
    (targetOnto : Function.Surjective target.encode) :
    (placement.withFlag flag separate).placeBit combinedOnto targetOnto
      (BinaryLabelEncoding.prodRightBit source .bool BinaryLabelEncoding.boolBit) = flag := by
  apply EncodedBit.eq_of_wire_eq
  rw [placeBit_wire]
  exact placement.withFlag_flag flag separate

end

end QuantumAlg.EncodedBit.WireSubsystem
