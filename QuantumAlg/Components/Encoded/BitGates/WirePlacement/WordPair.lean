/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import Mathlib.Data.Sum.Basic

/-!
# Word-pair placement from literal native coordinates

Two ordered words of distinct physical positions determine the complete
subsystem placement. Both operands use their actual big-endian wire order;
the target complement consists of all remaining existing positions.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Place a two-word arithmetic body on exactly the named physical operand bits. -/
def wordPairSubsystem (first second : Word encoding width)
    (firstDistinct : Function.Injective (fun index => (first.bit index).wire))
    (secondDistinct : Function.Injective (fun index => (second.bit index).wire))
    (separate : ∀ left right, (first.bit left).wire ≠ (second.bit right).wire) :
    WireSubsystem
      (.prod (BinaryLabelEncoding.finIdentity width) (BinaryLabelEncoding.finIdentity width))
      encoding where
  wires :=
    { toFun := fun index => Sum.elim (fun bit => (first.bit bit).wire)
        (fun bit => (second.bit bit).wire) (finSumFinEquiv.symm index)
      inj' := (firstDistinct.sumElim secondDistinct separate).comp
        finSumFinEquiv.symm.injective }

/-- Every first-operand position is the supplied first word position. -/
lemma wordPairSubsystem_left (first second : Word encoding width)
    (firstDistinct : Function.Injective (fun index => (first.bit index).wire))
    (secondDistinct : Function.Injective (fun index => (second.bit index).wire))
    (separate : ∀ left right, (first.bit left).wire ≠ (second.bit right).wire)
    (index : Fin width) :
    (wordPairSubsystem first second firstDistinct secondDistinct separate).wires
      (Fin.castAdd width index) = (first.bit index).wire := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.castAdd width index)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- Every second-operand position is the supplied second word position. -/
lemma wordPairSubsystem_right (first second : Word encoding width)
    (firstDistinct : Function.Injective (fun index => (first.bit index).wire))
    (secondDistinct : Function.Injective (fun index => (second.bit index).wire))
    (separate : ∀ left right, (first.bit left).wire ≠ (second.bit right).wire)
    (index : Fin width) :
    (wordPairSubsystem first second firstDistinct secondDistinct separate).wires
      (Fin.natAdd width index) = (second.bit index).wire := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.natAdd width index)) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

end

end QuantumAlg.EncodedBit
