/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Source

/-! # The complete original division label with only the numerical Y result replaced -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

attribute [local irreducible] Swap.step

private lemma raw_eq_withNumerator (first second : Window.Raw) (value : Word)
    (source : first.1.1.1.1 = second.1.1.1.1)
    (retained : frontier first = frontier second)
    (numerator : Frame.numerator first.1 = value) :
    first = withNumerator second value := by
  apply Prod.ext
  · apply Prod.ext
    · exact Prod.ext (Prod.ext source (congrArg Prod.fst retained)) numerator
    · exact congrArg (fun state : Pool 256 × (Frame.Controls × Window.Address) => state.2.1)
        retained
  · exact congrArg (fun state : Pool 256 × (Frame.Controls × Window.Address) => state.2.2)
      retained

private lemma withNumerator_congr (first second : Window.Raw) (value : Word)
    (same : first = second) : withNumerator first value = withNumerator second value :=
  congrArg (fun state => withNumerator state value) same

private lemma pool_eq_of_reads (first second : Window.Raw)
    (reads : ∀ bit : EncodedBit Frame.encoding, 256 ≤ bit.wire.val →
      (bit.wire.val < 580 ∨ 836 ≤ bit.wire.val) → bit.get first.1 = bit.get second.1) :
    first.1.1.1.2 = second.1.1.1.2 := by
  have onto : Function.Surjective (poolEncoding 256).encode :=
    product_total _ _ BitVec.equivFin.toEquiv.surjective
      (product_total _ _ BitVec.equivFin.toEquiv.surjective bool_total)
  apply EncodedBit.state_eq_of_get_eq onto
  intro observed
  let bit := Frame.scanBit (BinaryLabelEncoding.prodRightBit
    (MAU.Inversion.SharedEEA.encoding 256) (poolEncoding 256) observed)
  have position : bit.wire.val = 559 + observed.wire.val := by
    change (MAU.Inversion.SharedEEA.encoding 256).width + observed.wire.val = _
    rw [MAU.Inversion.SharedEEA.encoding_width]
    rfl
  have bound : observed.wire.val < 21 := by
    simpa only [poolEncoding_width, NumberTheory.SharedEEA.ScanMetadata.p256_poolWidth]
      using observed.wire.isLt
  exact reads bit (by rw [position]; omega) (Or.inl (by rw [position]; omega))

private lemma swap_pool (state : Window.Raw) : (Swap.step state).1.1.1.2 = state.1.1.1.2 :=
  pool_eq_of_reads _ _ (fun bit outsideA outsideY =>
    swap_pointBit_outside bit outsideA outsideY state)

private lemma flags_eq_of_reads (first second : Window.Raw)
    (control : Frame.pointControlBit.get first.1 = Frame.pointControlBit.get second.1)
    (normal : Frame.normalBit.get first.1 = Frame.normalBit.get second.1)
    (work : Frame.workBit.get first.1 = Frame.workBit.get second.1) :
    first.1.2 = second.1.2 :=
  Prod.ext control (Prod.ext normal work)

private lemma swap_flags (state : Window.Raw) : (Swap.step state).1.2 = state.1.2 :=
  flags_eq_of_reads _ _
    (swap_pointBit_outside Frame.pointControlBit
      (by norm_num only [Frame.pointControlBit_wire])
      (Or.inr (by norm_num only [Frame.pointControlBit_wire])) state)
    (swap_pointBit_outside Frame.normalBit (by norm_num only [Frame.normalBit_wire])
      (Or.inr (by norm_num only [Frame.normalBit_wire])) state)
    (swap_pointBit_outside Frame.workBit (by norm_num only [Frame.workBit_wire])
      (Or.inr (by norm_num only [Frame.workBit_wire])) state)

private lemma frontier_eq_of_components (first second : Window.Raw)
    (pool : first.1.1.1.2 = second.1.1.1.2) (flags : first.1.2 = second.1.2)
    (address : first.2 = second.2) : frontier first = frontier second :=
  Prod.ext pool (Prod.ext flags address)

private lemma swap_frontier (state : Window.Raw) : frontier (Swap.step state) = frontier state :=
  frontier_eq_of_components _ _ (swap_pool state) (swap_flags state) (swap_address state)

attribute [local irreducible] modulus Inversion.initial

private lemma division_active_frontier (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    frontier (Swap.step (activeDivisionAfterBackward stream width widthBound input positive bounded
      numerator flags address)) =
      frontier (activeDivisionInitial stream width widthBound input numerator flags address) := by
  let before := activeDivisionAfterForward stream width widthBound input positive bounded
    numerator flags address
  have arithmeticFlags := activeDivisionAfterForward_flags stream width widthBound input positive
    bounded numerator flags address
  have reset : frontier (afterReset .enable before) = frontier before :=
    Prod.ext (afterReset_pool .enable before arithmeticFlags)
      (Prod.ext (afterReset_flags .enable before arithmeticFlags)
        (afterReset_address .enable before))
  exact (swap_frontier _).trans
    ((division_afterBackward_frontier stream width widthBound input positive bounded numerator
      flags address).trans (reset.trans
        (restore_frontier_congr stream width widthBound _ _
          (clearedResult_frontier input positive bounded numerator flags address))))

lemma division_active_numerator (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (enabled : (Phase.physicalSelector .enable).get
      (activeDivisionAfterForward stream width widthBound input positive bounded numerator flags
        address).1 = true) :
    Frame.numerator (Swap.step (activeDivisionAfterBackward stream width widthBound input positive
      bounded numerator flags address)).1 =
      Save.savedWord (inverseWord input positive bounded)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true := by
  have words := division_afterBackward_words stream width widthBound input positive bounded
    numerator flags address
  have saved := afterReset_work1_value .enable
    (activeDivisionAfterForward stream width widthBound input positive bounded numerator flags
      address)
  rw [division_afterForward_work2, division_afterForward_numerator, enabled] at saved
  exact (Swap.step_numerator _).trans (words.2.2.trans
    ((prepare_word .work1 stream width widthBound _).trans saved))

/-- Full source, all pool systems, C/N/W and address are restored by the real complete call. -/
lemma division_active_eq (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (enabled : (Phase.physicalSelector .enable).get
      (activeDivisionAfterForward stream width widthBound input positive bounded numerator flags
        address).1 = true) :
    Swap.step (activeDivisionAfterBackward stream width widthBound input positive bounded numerator
      flags address) =
      withNumerator (activeDivisionInitial stream width widthBound input numerator flags address)
        (Save.savedWord (inverseWord input positive bounded)
          (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true) := by
  have retained := division_active_frontier stream width widthBound input positive bounded numerator
    flags address
  exact raw_eq_withNumerator _ _ _
    (division_active_source stream width widthBound input positive bounded numerator flags address)
    retained (division_active_numerator stream width widthBound input positive bounded numerator
      flags address enabled)

/-- Numerical division is conditional only on the original whole-digit predicate. -/
def divisionNumerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address)
    (admitted : divisionEnabled stream width bounded input numerator flags address = true →
      ActiveDomain input numerator) : Word :=
  if selected : divisionEnabled stream width bounded input numerator flags address = true then
    Save.savedWord (inverseWord input (admitted selected).positive (admitted selected).bounded)
      (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true
  else Frame.numerator (inputState stream width bounded input numerator flags address).1

private lemma divisionNumerator_selected (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (admitted : divisionEnabled stream width bounded input numerator flags address = true →
      ActiveDomain input numerator)
    (selected : divisionEnabled stream width bounded input numerator flags address = true) :
    divisionNumerator stream width bounded input numerator flags address admitted =
      Save.savedWord (inverseWord input (admitted selected).positive (admitted selected).bounded)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true :=
  dif_pos selected

private lemma divisionNumerator_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (admitted : divisionEnabled stream width bounded input numerator flags address = true →
      ActiveDomain input numerator)
    (selected : ¬ divisionEnabled stream width bounded input numerator flags address = true) :
    divisionNumerator stream width bounded input numerator flags address admitted =
      Frame.numerator (inputState stream width bounded input numerator flags address).1 :=
  dif_neg selected

attribute [local irreducible] divisionOutput divisionNumerator inputState

/-- A single complete output label covers arbitrary disabled words and selected field division. -/
lemma divisionOutput_eq (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address)
    (admitted : divisionEnabled stream width widthBound input numerator flags address = true →
      ActiveDomain input numerator) :
    divisionOutput stream width widthBound input numerator flags address admitted =
      withNumerator (inputState stream width widthBound input numerator flags address)
        (divisionNumerator stream width widthBound input numerator flags address admitted) := by
  by_cases selected : divisionEnabled stream width widthBound input numerator flags address = true
  · have domain := admitted selected
    let temporary := divisionFlags stream width widthBound input numerator flags address
    have enabled : (Phase.physicalSelector .enable).get
        (activeDivisionAfterForward stream width widthBound input domain.positive domain.bounded
          numerator temporary address).1 = true :=
      (division_forward_enable stream width widthBound input domain.positive domain.bounded
        numerator temporary address).trans
          ((divisionEnabled_setNormal stream width widthBound input numerator flags _ address).trans
            selected)
    have actual := division_active_eq stream width widthBound input domain.positive domain.bounded
      numerator temporary address enabled
    rw [divisionOutput_selected stream width widthBound input numerator flags address admitted
      selected, divisionNumerator_selected stream width widthBound input numerator flags address
        admitted selected]
    exact actual.trans (withNumerator_congr _ _ _
      (division_input_eq stream width widthBound input numerator flags normalZero address).symm)
  · rw [divisionOutput_disabled stream width widthBound input numerator flags address admitted
      selected, divisionNumerator_disabled stream width widthBound input numerator flags address
        admitted selected]
    exact (withNumerator_self _).symm

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
