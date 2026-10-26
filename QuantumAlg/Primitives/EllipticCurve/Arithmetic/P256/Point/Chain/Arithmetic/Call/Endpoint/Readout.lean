/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Multiplication

/-! # Complete returned source and original-coordinate readouts of the common call labels -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma scan_width : (MAU.Inversion.SharedEEA.Scanned.encoding 256).width = 580 :=
  MAU.Inversion.SharedEEA.Scanned.p256_encoding_width

private lemma point_read_of_wire (observed bit : EncodedBit Frame.encoding)
    (same : bit.wire = observed.wire) (first second : Window.Raw)
    (read : bit.get first.1 = bit.get second.1) :
    observed.get first.1 = observed.get second.1 := by
  have lens := EncodedBit.eq_of_wire_eq bit observed same
  exact (congrArg (fun value : EncodedBit Frame.encoding => value.get first.1) lens).symm.trans
    (read.trans (congrArg (fun value : EncodedBit Frame.encoding => value.get second.1) lens))

/-- Replacing Y changes no actual original source, pool, padding, history or C/N/W bit. -/
lemma withNumerator_other (observed : EncodedBit Frame.encoding)
    (outside : observed.wire.val < 580 ∨ 836 ≤ observed.wire.val)
    (state : Window.Raw) (value : Word) :
    observed.get (withNumerator state value).1 = observed.get state.1 := by
  rcases outside with before | after
  · let sourceBit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256) :=
      EncodedBit.fullBit (MAU.Inversion.SharedEEA.Scanned.encoding_surjective 256)
        ⟨observed.wire.val, by rw [scan_width]; exact before⟩
    refine point_read_of_wire observed (Frame.scanBit sourceBit) ?_
      (withNumerator state value) state rfl
    apply Fin.ext
    rfl
  · have bound : observed.wire.val < 839 := by
      simpa only [Frame.encoding_width] using observed.wire.isLt
    have positions : observed.wire.val = 836 ∨ observed.wire.val = 837 ∨
        observed.wire.val = 838 := by omega
    rcases positions with first | normal | work
    · exact point_read_of_wire observed Frame.pointControlBit
        (Fin.ext (Frame.pointControlBit_wire.trans first.symm)) _ _ rfl
    · exact point_read_of_wire observed Frame.normalBit
        (Fin.ext (Frame.normalBit_wire.trans normal.symm)) _ _ rfl
    · exact point_read_of_wire observed Frame.workBit
        (Fin.ext (Frame.workBit_wire.trans work.symm)) _ _ rfl

attribute [local irreducible] modulus inputState multiplicationOutput

/-- The complete original initialized source is restored; only the selected numerical Y changes. -/
lemma multiplicationOutput_eq (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    multiplicationOutput stream width bounded input numerator flags address =
      withNumerator (inputState stream width bounded input numerator flags address)
        (Save.savedWord
          (Frame.work2 (inputState stream width bounded input numerator flags address).1)
          (Frame.numerator (inputState stream width bounded input numerator flags address).1)
          flags.2.1) := by
  let original := inputState stream width bounded input numerator flags address
  have arithmeticFlags := inputState_flags stream width bounded input numerator flags address
  have selected : (Phase.physicalSelector .normal).get original.1 = flags.2.1 :=
    inputState_normal stream width bounded input numerator flags address
  have outputSame : multiplicationOutput stream width bounded input numerator flags address =
      Swap.step (afterReset .normal original) :=
    multiplicationOutput_step stream width bounded input numerator flags address
  rw [outputSame]
  apply window_eq_of_reads
  · exact (swap_afterReset_work1 .normal original).trans
      (inputState_work1 stream width bounded input numerator flags address).symm
  · exact (swap_afterReset_numerator .normal original).trans
      (congrArg (Save.savedWord (Frame.work2 original.1) (Frame.numerator original.1)) selected)
  · intro observed outsideA outsideY
    exact (swap_pointBit_outside observed outsideA outsideY (afterReset .normal original)).trans
      ((afterReset_other .normal observed outsideA outsideY original arithmeticFlags).trans
        (withNumerator_other observed outsideY original _).symm)
  · exact (swap_address (afterReset .normal original)).trans (afterReset_address .normal original)

lemma multiplicationOutput_numerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Frame.numerator (multiplicationOutput stream width bounded input numerator flags address).1 =
      Save.savedWord (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) flags.2.1 :=
  (congrArg (fun state : Window.Raw => Frame.numerator state.1)
    (multiplicationOutput_eq stream width bounded input numerator flags address)).trans
      (congrArg₂ (fun first second : Word => Save.savedWord first second flags.2.1)
        (inputState_work2 stream width bounded input numerator flags address)
        (inputState_numerator stream width bounded input numerator flags address))

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
