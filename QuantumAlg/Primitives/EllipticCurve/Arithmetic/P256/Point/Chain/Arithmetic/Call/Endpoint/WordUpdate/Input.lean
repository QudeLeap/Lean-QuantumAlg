/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.WordUpdate.Initial

/-!
# Complete Work2 updates, including all original padding and metadata

The three Work2 padding positions are proved zero from the symbolic
source initializer. The actual numerical setter preserves them. The
remaining original fields are reconstructed from their full erased
label, rather than inferred from the numerical payload alone.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open EncodedBit.WindowLookup MAU.Inversion.SharedEEA.Scanned

attribute [local implicit_reducible] capacity width

private lemma initial_input_tail (modulus : Nat)
    (input numerator : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) (index : Nat) (outside : modulus.size ≤ index) :
    (ControlledResident.initial modulus input numerator pool flags).1.1.1.secondWord.getMsbD
      index = false := by
  change (BitVec.equivFin.symm (MAU.Inversion.SharedEEA.InitialFrame.inputWord modulus
    input)).reverse.getMsbD index = false
  rw [BitVec.getMsbD_reverse]
  change input.val.testBit index = false
  exact Nat.testBit_eq_false_of_lt
    (input.isLt.trans_le (Nat.pow_le_pow_right (by decide) outside))

private lemma transport_secondWord {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) (index : Nat) :
    (Inversion.Transport.state same state).1.1.1.secondWord.getMsbD index =
      state.1.1.1.secondWord.getMsbD index := by
  cases same
  rfl

private lemma fixedPart_flip_work2 (index : Fin 256) (state : Window.Raw) :
    fixedPart (((Window.resultWord .work2).bit index).flip state) = fixedPart state := rfl

private lemma fixedPart_setWork2 (value : Word) (state : Window.Raw) :
    fixedPart (resultSetConstant (Window.resultWord .work2) value state) = fixedPart state := by
  unfold resultSetConstant EncodedBit.Word.xorConstantStep EncodedBit.Word.xorConstantGates
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact fixedPart_flip_work2 index

private def restoreInput (state : Window.Raw) (value : BitVec 259) : Window.Raw :=
  (((({ state.1.1.1.1 with secondWord := value }, state.1.1.1.2), state.1.1.2), state.1.2),
    state.2)

private lemma restoreInput_fixedPart (state : Window.Raw) :
    restoreInput (fixedPart state) state.1.1.1.1.secondWord = state := rfl

private lemma raw_eq_of_fixedPart (first second : Window.Raw)
    (fixed : fixedPart first = fixedPart second)
    (word : first.1.1.1.1.secondWord = second.1.1.1.1.secondWord) : first = second :=
  (restoreInput_fixedPart first).symm.trans
    ((congrArg₂ restoreInput fixed word).trans (restoreInput_fixedPart second))

private def sourceWordBit (index : Fin 259) : EncodedBit Window.encoding :=
  Window.pointBit (Frame.scanBit (sourceBit 256
    (MAU.Inversion.SharedEEA.secondWordBit 256 index)))

private lemma sourceWordBit_read (index : Fin 259) (state : Window.Raw) :
    (sourceWordBit index).get state = state.1.1.1.1.secondWord.getMsbD index.val :=
  MAU.Inversion.SharedEEA.secondWordBit_get 256 index state.1.1.1.1

private lemma work2_read (index : Fin 256) (state : Window.Raw) :
    ((Window.resultWord .work2).bit index).get state =
      state.1.1.1.1.secondWord.getMsbD index.val :=
  sourceWordBit_read ⟨index.val, by omega⟩ state

private lemma work2_value_read (index : Fin 256) (state : Window.Raw) :
    ((Window.resultWord .work2).bit index).get state =
      (Frame.work2 state.1).val.testBit index.val :=
  WordPort.bit_get .work2 index state.1

private lemma setWork2_tail (index : Fin 259) (outside : 256 ≤ index.val)
    (value : Word) (state : Window.Raw) :
    (resultSetConstant (Window.resultWord .work2) value state).1.1.1.1.secondWord.getMsbD
        index.val = state.1.1.1.1.secondWord.getMsbD index.val := by
  have position : (sourceWordBit index).wire.val = 259 + index.val := rfl
  have read := resultSetConstant_observed (Window.resultWord .work2) value (sourceWordBit index)
    (by
      intro bit same
      have positions := congrArg Fin.val same
      rw [Window.resultWord_wire, position] at positions
      simp only [WordPort.physicalIndex] at positions
      have within := bit.isLt
      omega) state
  exact (sourceWordBit_read index _).symm.trans (read.trans (sourceWordBit_read index state))

private lemma setWork2_eq_of_components (first second : Window.Raw) (value : Word)
    (fixed : fixedPart first = fixedPart second) (word : Frame.work2 second.1 = value)
    (tail : ∀ index : Fin 259, 256 ≤ index.val →
      first.1.1.1.1.secondWord.getMsbD index.val =
        second.1.1.1.1.secondWord.getMsbD index.val) :
    resultSetConstant (Window.resultWord .work2) value first = second := by
  apply raw_eq_of_fixedPart
  · exact (fixedPart_setWork2 value first).trans fixed
  · apply BitVec.eq_of_getMsbD_eq
    intro index within
    by_cases inside : index < 256
    · let bit : Fin 256 := ⟨index, inside⟩
      have actual := resultSetConstant_get (Window.resultWord .work2)
        (Window.resultWord_distinct .work2) value first bit
      have requested := (work2_value_read bit second).trans
        (congrArg (fun value : Word => value.val.testBit bit.val) word)
      exact (work2_read bit _).symm.trans
        (actual.trans (requested.symm.trans (work2_read bit second)))
    · let bit : Fin 259 := ⟨index, within⟩
      exact (setWork2_tail bit (Nat.le_of_not_gt inside) value first).trans
        (tail bit (Nat.le_of_not_gt inside))

attribute [local irreducible] modulus

private lemma clearedInitial_input_tail (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) (index : Nat) (outside : 256 ≤ index) :
    (clearedInitial input numerator flags address).1.1.1.1.secondWord.getMsbD index = false :=
  (transport_secondWord Inversion.modulus_size _ index).trans
    (initial_input_tail modulus input numerator (0, (0, false)) flags index
      (by rw [Inversion.modulus_size]; exact outside))

/-- All 259 source positions and every other initialized field match the updated original X. -/
lemma clearedInitial_setWork2
    (first second numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    resultSetConstant (Window.resultWord .work2)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second)
        (clearedInitial first numerator flags address) =
      clearedInitial second numerator flags address := by
  apply setWork2_eq_of_components
  · exact clearedInitial_fixedPart first second numerator flags address
  · exact Inversion.initial_value second numerator (0, (0, false)) flags
  · intro index outside
    exact (clearedInitial_input_tail first numerator flags address index.val outside).trans
      (clearedInitial_input_tail second numerator flags address index.val outside).symm

private lemma fixedPart_digit (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) (state : Window.Raw) :
    (Window.Enable.digitBit stream width bounded index).get (fixedPart state) =
      (Window.Enable.digitBit stream width bounded index).get state := by
  refine Fin.cases ?_ (fun _ => ?_) index
  · unfold Window.Enable.digitBit Window.streamBit
    split <;> rfl
  · rfl

private lemma fixedPart_enable (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    fixedPart (Window.Enable.step stream width bounded state) =
      Window.Enable.step stream width bounded (fixedPart state) := by
  have same :
      (∀ index, (Window.Enable.digitBit stream width bounded index).get
        (fixedPart state) = false) ↔
      (∀ index, (Window.Enable.digitBit stream width bounded index).get state = false) :=
    forall_congr' (fun index => by rw [fixedPart_digit])
  unfold Window.Enable.step Window.Enable.toggleStep
  change fixedPart
      (if ∀ index, (Window.Enable.digitBit stream width bounded index).get state = false
        then state else Window.Enable.outputBit.flip state) =
    (if ∀ index, (Window.Enable.digitBit stream width bounded index).get (fixedPart state) = false
      then fixedPart state else Window.Enable.outputBit.flip (fixedPart state))
  by_cases zero : ∀ index, (Window.Enable.digitBit stream width bounded index).get state = false
  · rw [if_pos zero, if_pos (same.mpr zero)]
  · rw [if_neg zero, if_neg (fun matched => zero (same.mp matched))]
    rfl

private lemma inputState_fixedPart (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    fixedPart (inputState stream width bounded first numerator flags address) =
      fixedPart (inputState stream width bounded second numerator flags address) := by
  change fixedPart (Window.Enable.step stream width bounded
      (clearedInitial first numerator flags address)) =
    fixedPart (Window.Enable.step stream width bounded
      (clearedInitial second numerator flags address))
  exact (fixedPart_enable stream width bounded _).trans
    ((congrArg (Window.Enable.step stream width bounded)
      (clearedInitial_fixedPart first second numerator flags address)).trans
        (fixedPart_enable stream width bounded _).symm)

private lemma inputState_input_tail (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) (index : Nat) (outside : 256 ≤ index) :
    (inputState stream width bounded input numerator flags address).1.1.1.1.secondWord.getMsbD
      index = false := by
  have source : (inputState stream width bounded input numerator flags address).1.1.1.1 =
      (clearedInitial input numerator flags address).1.1.1.1 :=
    enable_source stream width bounded (clearedInitial input numerator flags address)
  exact (congrArg (fun state : MAU.Inversion.SharedEEA.Registers 256 =>
    state.secondWord.getMsbD index) source).trans
      (clearedInitial_input_tail input numerator flags address index outside)

/-- The live-F input label also admits an exact original X update with no metadata assumption. -/
lemma inputState_setWork2 (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    resultSetConstant (Window.resultWord .work2)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second)
        (inputState stream width bounded first numerator flags address) =
      inputState stream width bounded second numerator flags address := by
  apply setWork2_eq_of_components
  · exact inputState_fixedPart stream width bounded first second numerator flags address
  · exact inputState_work2 stream width bounded second numerator flags address
  · intro index outside
    exact (inputState_input_tail stream width bounded first numerator flags address index.val
      outside).trans
        (inputState_input_tail stream width bounded second numerator flags address index.val
          outside).symm

/-- The real enable inverse returns the complete updated source and its zero original pool. -/
lemma clearEnable_setWork2 (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.Enable.step stream width bounded
      (resultSetConstant (Window.resultWord .work2)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second)
        (inputState stream width bounded first numerator flags address)) =
      clearedInitial second numerator flags address :=
  (congrArg (Window.Enable.step stream width bounded)
    (inputState_setWork2 stream width bounded first second numerator flags address)).trans
      (inputState_clear stream width bounded second numerator flags address)

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
