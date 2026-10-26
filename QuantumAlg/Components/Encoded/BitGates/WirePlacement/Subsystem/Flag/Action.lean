/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Identical full actions when an existing output flag is retained

Adding the original flag to a semantic subsystem and retaining its value
does not change the complete physical action. Every source and outside
wire is compared explicitly; this certificate constructs no program.
-/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target} (placement : WireSubsystem source target)

/-- Both complete groupings read the same original source beside the retained flag. -/
lemma withFlag_grouping_source (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire)
    (sourceOnto : Function.Surjective source.encode)
    (combinedOnto : Function.Surjective (BinaryLabelEncoding.prod source .bool).encode)
    (targetOnto : Function.Surjective target.encode) (state : Target) :
    (((placement.withFlag flag separate).full combinedOnto targetOnto).grouping state).1.1 =
      ((placement.full sourceOnto targetOnto).grouping state).1 := by
  apply state_eq_of_get_eq sourceOnto
  intro bit
  let observed := fullBit targetOnto (placement.wires bit.wire)
  have left := (placement.withFlag flag separate).full_source_read combinedOnto targetOnto
    (BinaryLabelEncoding.prodLeftBit source .bool bit) observed
    (placement.withFlag_source flag separate bit.wire) state
  have right := placement.full_source_read sourceOnto targetOnto bit observed rfl state
  exact left.trans right.symm

/-- Retaining an explicitly included original flag leaves the same complete source action. -/
lemma withFlag_step (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire)
    (sourceOnto : Function.Surjective source.encode)
    (combinedOnto : Function.Surjective (BinaryLabelEncoding.prod source .bool).encode)
    (targetOnto : Function.Surjective target.encode)
    (action : Source → Source) (state : Target) :
    ((placement.withFlag flag separate).full combinedOnto targetOnto).step
        (fun pair => ((action pair.1.1, pair.1.2), pair.2)) state =
      (placement.full sourceOnto targetOnto).step
        (fun pair => (action pair.1, pair.2)) state := by
  apply state_eq_of_get_eq targetOnto
  intro observed
  by_cases inside : observed.wire ∈ Set.range placement.wires
  · obtain ⟨wire, location⟩ := inside
    let bit := fullBit sourceOnto wire
    have selected :
        (placement.withFlag flag separate).wires
          (BinaryLabelEncoding.prodLeftBit source .bool bit).wire = observed.wire :=
      (placement.withFlag_source flag separate wire).trans location
    have left := (placement.withFlag flag separate).full_step_source_read
      combinedOnto targetOnto (BinaryLabelEncoding.prodLeftBit source .bool bit)
      observed selected (fun pair => (action pair.1, pair.2)) state
    change observed.get _ = bit.get (action
      (((placement.withFlag flag separate).full combinedOnto targetOnto).grouping state).1.1)
      at left
    rw [placement.withFlag_grouping_source flag separate sourceOnto combinedOnto
      targetOnto state] at left
    exact left.trans (placement.full_step_source_read sourceOnto targetOnto bit observed
      location action state).symm
  · have base := placement.full_step_other_read sourceOnto targetOnto observed inside action state
    by_cases same : flag.wire = observed.wire
    · have selected : (placement.withFlag flag separate).wires
          (BinaryLabelEncoding.prodRightBit source .bool BinaryLabelEncoding.boolBit).wire =
            observed.wire := (placement.withFlag_flag flag separate).trans same
      have left := (placement.withFlag flag separate).full_step_source_read
        combinedOnto targetOnto
        (BinaryLabelEncoding.prodRightBit source .bool BinaryLabelEncoding.boolBit)
        observed selected (fun pair => (action pair.1, pair.2)) state
      have original := (placement.withFlag flag separate).full_source_read
        combinedOnto targetOnto
        (BinaryLabelEncoding.prodRightBit source .bool BinaryLabelEncoding.boolBit)
        observed selected state
      exact (left.trans original).trans base.symm
    · have outside : observed.wire ∉ Set.range (placement.withFlag flag separate).wires := by
        rintro ⟨wire, location⟩
        obtain ⟨selected, rfl⟩ := finSumFinEquiv.surjective wire
        cases selected with
        | inl index =>
            exact inside ⟨index,
              (placement.withFlag_source flag separate index).symm.trans location⟩
        | inr index =>
            have zero : index = (0 : Fin 1) := by
              apply Fin.ext
              change index.val = 0
              have within := index.isLt
              change index.val < 1 at within
              omega
            subst index
            exact same ((placement.withFlag_flag flag separate).symm.trans location)
      exact ((placement.withFlag flag separate).full_step_other_read
        combinedOnto targetOnto observed outside (fun pair => (action pair.1, pair.2)) state).trans
          base.symm

end

end QuantumAlg.EncodedBit.WireSubsystem
