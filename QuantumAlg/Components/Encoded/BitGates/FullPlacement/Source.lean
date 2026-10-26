/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.FullFrame

/-!
# Complete actions agree on identical original source positions

Different encodings or orders of the saved complement do not change a
source action when every original source position agrees. This is a
full-state equality and introduces no executed permutation.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Saved OtherSaved Target : Type}
    {source : BinaryLabelEncoding Source} {saved : BinaryLabelEncoding Saved}
    {otherSaved : BinaryLabelEncoding OtherSaved} {target : BinaryLabelEncoding Target}

/-- The actual source positions of a complete product frame form an existing subsystem. -/
def sourceSubsystem (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target) :
    WireSubsystem source target where
  wires :=
    { toFun := fun index => whole.mappedWire (Fin.castAdd saved.width index)
      inj' := by
        intro left right same
        apply Fin.ext
        exact congrArg (fun index : Fin (source.width + saved.width) => index.val)
          (whole.mappedWire_injective same) }

/-- Identical source positions and retained full complements determine identical full actions. -/
lemma step_eq_of_source_wires
    (left : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (right : FullPlacement (BinaryLabelEncoding.prod source otherSaved) target)
    (sourceOnto : Function.Surjective source.encode)
    (savedOnto : Function.Surjective saved.encode)
    (otherSavedOnto : Function.Surjective otherSaved.encode)
    (targetOnto : Function.Surjective target.encode)
    (same : ∀ index : Fin source.width,
      left.mappedWire (Fin.castAdd saved.width index) =
        right.mappedWire (Fin.castAdd otherSaved.width index))
    (action : Source → Source) (state : Target) :
    left.step (fun pair => (action pair.1, pair.2)) state =
      right.step (fun pair => (action pair.1, pair.2)) state := by
  have first := left.sourceSubsystem.full_step_eq_fullFrame sourceOnto savedOnto targetOnto
    left (fun _ => rfl) action state
  have second := left.sourceSubsystem.full_step_eq_fullFrame sourceOnto otherSavedOnto targetOnto
    right (fun index => (same index).symm) action state
  exact first.symm.trans second

end

end QuantumAlg.EncodedBit.FullPlacement
