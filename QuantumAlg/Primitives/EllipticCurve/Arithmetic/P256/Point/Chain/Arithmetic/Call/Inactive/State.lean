/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.State

/-!
# Complete inactive label restoration after the actual save, reset and swap

The original Y is arbitrary. It was saved into clean A before H and physical
measurement; only afterward is Y zero. The unconditional actual numerical
swap restores A and Y and every retained source, pool, control and address
coordinate. No inactive canonical-value premise is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

attribute [local irreducible] Swap.step afterReset

private lemma swap_pointBit_outside (observed : EncodedBit Frame.encoding)
    (outsideA : 256 ≤ observed.wire.val)
    (outsideY : observed.wire.val < 580 ∨ 836 ≤ observed.wire.val)
    (state : Window.Raw) :
    observed.get (Swap.step state).1 = observed.get state.1 := by
  have outside : (256 ≤ (Window.pointBit observed).wire.val ∧
      (Window.pointBit observed).wire.val < 580) ∨
      836 ≤ (Window.pointBit observed).wire.val := by
    simp only [Window.pointBit_wire]
    omega
  exact Swap.step_outside (Window.pointBit observed) outside state

private lemma work1_eq_get (first second : Window.Raw)
    (sameWord : Frame.work1 first.1 = Frame.work1 second.1)
    (observed : EncodedBit Frame.encoding) (inside : observed.wire.val < 256) :
    observed.get first.1 = observed.get second.1 := by
  let index : Fin 256 := ⟨observed.wire.val, inside⟩
  have same : ((Window.resultWord .work1).bit index).wire =
      (Window.pointBit observed).wire := by
    apply Fin.ext
    rw [Window.resultWord_wire, Window.pointBit_wire]
    rfl
  have lens := EncodedBit.eq_of_wire_eq _ _ same
  have firstRead := congrArg (fun bit : EncodedBit Window.encoding => bit.get first) lens
  have secondRead := congrArg (fun bit : EncodedBit Window.encoding => bit.get second) lens
  have wordRead := (WordPort.bit_get .work1 index first.1).trans
    ((congrArg (fun value : Word => value.val.testBit index.val) sameWord).trans
      (WordPort.bit_get .work1 index second.1).symm)
  exact firstRead.symm.trans (wordRead.trans secondRead)

private lemma numerator_eq_get (first second : Window.Raw)
    (sameWord : Frame.numerator first.1 = Frame.numerator second.1)
    (observed : EncodedBit Frame.encoding)
    (inside : 580 ≤ observed.wire.val ∧ observed.wire.val < 836) :
    observed.get first.1 = observed.get second.1 := by
  let index : Fin 256 := ⟨835 - observed.wire.val, by omega⟩
  have same : ((Window.resultWord .numerator).bit index).wire =
      (Window.pointBit observed).wire := by
    apply Fin.ext
    rw [Window.resultWord_wire, Window.pointBit_wire]
    change 580 + (255 - (835 - observed.wire.val)) = observed.wire.val
    omega
  have lens := EncodedBit.eq_of_wire_eq _ _ same
  have firstRead := congrArg (fun bit : EncodedBit Window.encoding => bit.get first) lens
  have secondRead := congrArg (fun bit : EncodedBit Window.encoding => bit.get second) lens
  have wordRead := (WordPort.bit_get .numerator index first.1).trans
    ((congrArg (fun value : Word => value.val.testBit index.val) sameWord).trans
      (WordPort.bit_get .numerator index second.1).symm)
  exact firstRead.symm.trans (wordRead.trans secondRead)

private lemma window_eq_of_reads (first second : Window.Raw)
    (accumulator : Frame.work1 first.1 = Frame.work1 second.1)
    (numerator : Frame.numerator first.1 = Frame.numerator second.1)
    (outside : ∀ observed : EncodedBit Frame.encoding,
      256 ≤ observed.wire.val → (observed.wire.val < 580 ∨ 836 ≤ observed.wire.val) →
        observed.get first.1 = observed.get second.1)
    (address : first.2 = second.2) : first = second := by
  apply Prod.ext
  · apply EncodedBit.state_eq_of_get_eq Frame.encoding_surjective
    intro observed
    by_cases inAccumulator : observed.wire.val < 256
    · exact work1_eq_get first second accumulator observed inAccumulator
    · by_cases inNumerator : 580 ≤ observed.wire.val ∧ observed.wire.val < 836
      · exact numerator_eq_get first second numerator observed inNumerator
      · exact outside observed (Nat.le_of_not_gt inAccumulator)
          ((not_and_or.mp inNumerator).imp Nat.lt_of_not_ge Nat.le_of_not_gt)
  · exact address

private lemma address_eq_of_reads (first second : Window.Raw)
    (reads : ∀ index, (Window.addressBit index).get first =
      (Window.addressBit index).get second) : first.2 = second.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have reflected : 14 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have within := index.isLt
    omega
  have read := reads index.rev
  simpa only [Window.addressBit_get, reflected] using read

private lemma swap_address (state : Window.Raw) : (Swap.step state).2 = state.2 :=
  address_eq_of_reads (Swap.step state) state (fun index => Swap.step_address index state)

lemma swap_afterReset_disabled (selection : Selector) (state : Window.Raw)
    (zero : Save.ports.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (disabled : (Phase.physicalSelector selection).get state.1 = false) :
    Swap.step (afterReset selection state) = state := by
  have accumulator : Frame.work1 (Swap.step (afterReset selection state)).1 =
      Frame.work1 state.1 := (swap_afterReset_work1 selection state).trans zero.symm
  have numerator : Frame.numerator (Swap.step (afterReset selection state)).1 =
      Frame.numerator state.1 := by
    simpa only [disabled, Save.savedWord, Bool.false_eq_true, ↓reduceIte] using
      swap_afterReset_numerator selection state
  apply window_eq_of_reads _ state accumulator numerator
  · intro observed outsideA outsideY
    exact (swap_pointBit_outside observed outsideA outsideY (afterReset selection state)).trans
      (afterReset_other selection observed outsideA outsideY state flags)
  · exact (swap_address (afterReset selection state)).trans (afterReset_address selection state)

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
