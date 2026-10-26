/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Resident
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total

/-!
# Concrete complete labels between actual arithmetic saving and reset

These are the actual Save basis endpoint and the named physical-reset
branch endpoint. Original source fields outside A, the full pool, C/N/W
and the address are retained by physical readouts, rather than guessed
from three numerical words. No reset is added to the native prefix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

private lemma originalSource_width : (MAU.Inversion.SharedEEA.encoding 256).width = 559 := by
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

/-- Complete endpoint of the actual saved-product program, with the original address retained. -/
def afterSave (selection : Selector) (state : Window.Raw) : Window.Raw :=
  (Save.savedState Save.ports selection state.1, state.2)

/-- The physical Y reset branch endpoint retains the actual saved A and complete source. -/
def afterReset (selection : Selector) (state : Window.Raw) : Window.Raw :=
  Reset.namedOutcome .numerator Reset.zeroOutcome (afterSave selection state)

lemma save_apply (selection : Selector) (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) (zero : Save.ports.target.value state.1 = Horner.zeroWord)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (admitted : (selectorBit Save.ports selection).get
      ((Placement.layout Save.ports).grouping state.1).2.2 = true →
        Canonical (Save.ports.source.value state.1)) :
    (Window.suffixProgram (Save.program Save.ports selection)).applyNormalized environment
      (Window.ket state) = Window.ket (afterSave selection state) :=
  suffix_apply _ environment state.1 _ state.2
    (Save.program_apply_of_flags Save.ports selection environment state.1 zero flags admitted)

lemma afterReset_numerator (selection : Selector) (state : Window.Raw) :
    Frame.numerator (afterReset selection state).1 = Reset.zeroOutcome :=
  Reset.namedOutcome_value .numerator Reset.zeroOutcome (afterSave selection state)

lemma afterReset_work1 (selection : Selector) (state : Window.Raw) :
    Frame.work1 (afterReset selection state).1 = Frame.work1 (afterSave selection state).1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have below : (Window.pointBit (WordPort.bit .work1 index)).wire.val < 580 := by
    rw [Window.pointBit_wire, WordPort.bit_wire]
    change index.val < 580
    omega
  have read := Reset.namedOutcome_numerator_outside Reset.zeroOutcome
    (Window.pointBit (WordPort.bit .work1 index)) (Or.inl below) (afterSave selection state)
  simpa only [afterReset, Window.pointBit_get, WordPort.bit_get, WordPort.value] using read

/-- The physical saved A contains exactly the same selected product used by the paid phase. -/
lemma afterReset_work1_value (selection : Selector) (state : Window.Raw) :
    Frame.work1 (afterReset selection state).1 =
      Save.savedWord (Frame.work2 state.1) (Frame.numerator state.1)
        ((Phase.physicalSelector selection).get state.1) := by
  have selected := Phase.selector_get Save.ports selection state.1
  exact (afterReset_work1 selection state).trans
    ((Save.savedState_target Save.ports selection state.1).trans
      (congrArg (Save.savedWord (Frame.work2 state.1) (Frame.numerator state.1)) selected.symm))

/-- The actual unconditional swap sends the physical reset zero back to A. -/
lemma swap_afterReset_work1 (selection : Selector) (state : Window.Raw) :
    Frame.work1 (Swap.step (afterReset selection state)).1 = Reset.zeroOutcome :=
  (Swap.step_work1 (afterReset selection state)).trans (afterReset_numerator selection state)

/-- Inactive old Y and active products use the same actual numerical swap. -/
lemma swap_afterReset_numerator (selection : Selector) (state : Window.Raw) :
    Frame.numerator (Swap.step (afterReset selection state)).1 =
      Save.savedWord (Frame.work2 state.1) (Frame.numerator state.1)
        ((Phase.physicalSelector selection).get state.1) :=
  (Swap.step_numerator (afterReset selection state)).trans (afterReset_work1_value selection state)

/-- Every actual original coordinate outside A and Y survives Save followed by physical Y reset. -/
lemma afterReset_other (selection : Selector) (observed : EncodedBit Frame.encoding)
    (outsideA : 256 ≤ observed.wire.val)
    (outsideY : observed.wire.val < 580 ∨ 836 ≤ observed.wire.val)
    (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    observed.get (afterReset selection state).1 = observed.get state.1 := by
  have resetRead := Reset.namedOutcome_numerator_outside Reset.zeroOutcome
    (Window.pointBit observed) (by simpa only [Window.pointBit_wire] using outsideY)
    (afterSave selection state)
  have saveRead := Save.savedState_other Save.ports selection observed (by
    intro index same
    have positions := congrArg Fin.val same
    rw [WordPort.bit_wire] at positions
    change index.val = observed.wire.val at positions
    have bound := index.isLt
    omega) state.1 flags
  exact resetRead.trans saveRead


/-- The separate F and N physical controls survive the actual save and physical Y reset. -/
lemma afterReset_selector (selection observed : Selector) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    (Phase.physicalSelector observed).get (afterReset selection state).1 =
      (Phase.physicalSelector observed).get state.1 := by
  cases observed
  · exact afterReset_other selection Native.BorrowedControl.flag
      (by rw [Native.BorrowedControl.flag_wire]; omega)
      (Or.inl (by rw [Native.BorrowedControl.flag_wire]; omega)) state flags
  · exact afterReset_other selection Frame.normalBit
      (by rw [Frame.normalBit_wire]; omega)
      (Or.inr (by rw [Frame.normalBit_wire]; omega)) state flags

/-- Every original EEA source coordinate outside the saved A payload is retained. -/
lemma afterReset_source (selection : Selector) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding 256))
    (outsideA : 256 ≤ observed.wire.val) :
    observed.get (afterReset selection state).1.1.1.1 = observed.get state.1.1.1.1 := by
  let lifted : EncodedBit Frame.encoding := Frame.scanBit
    (BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding 256)
      (MAU.Inversion.SharedEEA.Scanned.poolEncoding 256) observed)
  have position : lifted.wire.val = observed.wire.val := rfl
  have bound : observed.wire.val < 559 := by
    simpa only [originalSource_width] using observed.wire.isLt
  exact afterReset_other selection lifted (by rw [position]; exact outsideA)
    (Or.inl (by rw [position]; omega)) state flags

private lemma sourceAt_retained {width : Nat} (same : width = 256)
    (initial final : Frame.Raw)
    (retained : ∀ observed : EncodedBit (MAU.Inversion.SharedEEA.encoding 256),
      256 ≤ observed.wire.val →
        observed.get final.1.1.1 = observed.get initial.1.1.1)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding width))
    (outsideA : width ≤ observed.wire.val) :
    observed.get (Boundary.sourceAt same final).1.1.1 =
      observed.get (Boundary.sourceAt same initial).1.1.1 := by
  cases same
  exact retained observed outsideA

section

attribute [local irreducible] modulus Boundary.sourceAt afterReset

/-- The same complete source retention holds in the actual resident modulus-width carrier. -/
lemma afterReset_source_typed (selection : Selector) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size))
    (outsideA : modulus.size ≤ observed.wire.val) :
    observed.get (Boundary.source (afterReset selection state).1).1.1.1 =
      observed.get (Boundary.source state.1).1.1.1 :=
  sourceAt_retained (width := modulus.size) Inversion.modulus_size state.1
    (afterReset selection state).1 (afterReset_source selection state flags) observed outsideA

end

/-- Every one of the twenty-one original pool systems retains its actual value. -/
lemma afterReset_pool (selection : Selector) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    (afterReset selection state).1.1.1.2 = state.1.1.1.2 := by
  have onto : Function.Surjective
      (MAU.Inversion.SharedEEA.Scanned.poolEncoding 256).encode :=
    MAU.Inversion.SharedEEA.Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective
      (MAU.Inversion.SharedEEA.Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective
        MAU.Inversion.SharedEEA.Scanned.bool_total)
  apply EncodedBit.state_eq_of_get_eq onto
  intro observed
  let lifted : EncodedBit Frame.encoding := Frame.scanBit
    (BinaryLabelEncoding.prodRightBit (MAU.Inversion.SharedEEA.encoding 256)
      (MAU.Inversion.SharedEEA.Scanned.poolEncoding 256) observed)
  have position : lifted.wire.val = 559 + observed.wire.val := by
    change (MAU.Inversion.SharedEEA.encoding 256).width + observed.wire.val = _
    rw [MAU.Inversion.SharedEEA.encoding_width]
    rfl
  have bound : observed.wire.val < 21 := by
    simpa only [MAU.Inversion.SharedEEA.Scanned.poolEncoding_width,
      NumberTheory.SharedEEA.ScanMetadata.p256_poolWidth] using observed.wire.isLt
  have read := afterReset_other selection lifted
    (by rw [position]; omega) (Or.inl (by rw [position]; omega)) state flags
  exact read

/-- Physical Y reset and product saving preserve the original EEA Ctrl field. -/
lemma afterReset_control (selection : Selector) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    (afterReset selection state).1.1.1.1.control = state.1.1.1.1.control := by
  have read := afterReset_source selection state flags
    (MAU.Inversion.SharedEEA.controlBit 256) (by
      rw [MAU.Inversion.SharedEEA.controlBit_wire]
      omega)
  simpa only [MAU.Inversion.SharedEEA.controlBit_get] using read

/-- Clearing F leaves the complete original EEA source, including every metadata bit, unchanged. -/
lemma enable_source (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    (Window.Enable.step stream width bounded state).1.1.1.1 = state.1.1.1.1 := by
  apply EncodedBit.state_eq_of_get_eq (MAU.Inversion.SharedEEA.encoding_surjective 256)
  intro observed
  let lifted : EncodedBit Window.encoding := Window.pointBit (Frame.scanBit
    (BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding 256)
      (MAU.Inversion.SharedEEA.Scanned.poolEncoding 256) observed))
  have bound : observed.wire.val < 559 := by
    simpa only [originalSource_width] using observed.wire.isLt
  exact Window.Enable.step_other stream width bounded lifted (by
    intro same
    have position := congrArg Fin.val same
    rw [Window.Enable.outputBit_wire] at position
    change 560 = observed.wire.val at position
    omega) state

/-- The actual temporary F-to-N transfer also leaves the entire original EEA source unchanged. -/
lemma prepare_source (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    (Control.prepareStep stream width bounded state).1.1.1.1 = state.1.1.1.1 := by
  apply EncodedBit.state_eq_of_get_eq (MAU.Inversion.SharedEEA.encoding_surjective 256)
  intro observed
  let lifted : EncodedBit Window.encoding := Window.pointBit (Frame.scanBit
    (BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding 256)
      (MAU.Inversion.SharedEEA.Scanned.poolEncoding 256) observed))
  have bound : observed.wire.val < 559 := by
    simpa only [originalSource_width] using observed.wire.isLt
  apply Control.prepare_other stream width bounded lifted
  · intro same
    have position := congrArg Fin.val same
    rw [Window.Enable.outputBit_wire] at position
    change 560 = observed.wire.val at position
    omega
  · intro same
    have position := congrArg Fin.val same
    rw [Window.normalBit_wire] at position
    change 837 = observed.wire.val at position
    omega

/-- The actual three arithmetic flags remain zero for the phase's different word assignment. -/
lemma afterReset_arithmeticFlags (selection : Selector) (assignment : PortAssignment)
    (state : Window.Raw) :
    ((Placement.layout assignment).grouping (afterReset selection state).1).1.1.2 = false ∧
      ((Placement.layout assignment).grouping (afterReset selection state).1).1.2.1 = false ∧
        ((Placement.layout assignment).grouping (afterReset selection state).1).1.2.2 = false := by
  have zeros (index : Fin 3) :
      (arithmeticFlag index).get (afterReset selection state).1 = false := by
    have outside : (Window.pointBit (arithmeticFlag index)).wire.val < 580 := by
      rw [Window.pointBit_wire, arithmeticFlag_wire]
      unfold arithmeticFlagIndex
      split_ifs <;> omega
    have resetRead := Reset.namedOutcome_numerator_outside Reset.zeroOutcome
      (Window.pointBit (arithmeticFlag index)) (Or.inl outside) (afterSave selection state)
    exact resetRead.trans (Save.flag_zero Save.ports index _
      (Save.savedState_flags Save.ports selection state.1))
  exact ⟨(Placement.arithmeticFlagPort_get assignment ⟨0, by decide⟩ _).trans (zeros 0),
    (Placement.arithmeticFlagPort_get assignment ⟨1, by decide⟩ _).trans (zeros 1),
    (Placement.arithmeticFlagPort_get assignment ⟨2, by decide⟩ _).trans (zeros 2)⟩

/-- The same physical address remains available to clear F after the actual save/reset. -/
lemma afterReset_address (selection : Selector) (state : Window.Raw) :
    (afterReset selection state).2 = state.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have reflected : 14 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have within := index.isLt
    omega
  have outside : 836 ≤ (Window.addressBit index.rev).wire.val := by
    rw [Window.addressBit_wire]
    omega
  have read := Reset.namedOutcome_numerator_outside Reset.zeroOutcome
    (Window.addressBit index.rev) (Or.inr outside) (afterSave selection state)
  simpa only [Window.addressBit_get, reflected, afterReset, afterSave] using read

/-- C, genuine N and arbitrary W retain their separate original physical meanings. -/
lemma afterReset_flags (selection : Selector) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    (afterReset selection state).1.2 = state.1.2 := by
  have control := afterReset_other selection Frame.pointControlBit
    (by rw [Frame.pointControlBit_wire]; omega)
    (Or.inr (by rw [Frame.pointControlBit_wire])) state flags
  have normal := afterReset_other selection Frame.normalBit
    (by rw [Frame.normalBit_wire]; omega)
    (Or.inr (by rw [Frame.normalBit_wire]; omega)) state flags
  have work := afterReset_other selection Frame.workBit
    (by rw [Frame.workBit_wire]; omega)
    (Or.inr (by rw [Frame.workBit_wire]; omega)) state flags
  exact Prod.ext control (Prod.ext normal work)


/-- Save and reset retain every actual address digit used to clear the enable. -/
lemma afterReset_digit (selection : Selector) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (index : Fin (width + 1)) :
    (Window.Enable.digitBit stream width bounded index).get (afterReset selection state) =
      (Window.Enable.digitBit stream width bounded index).get state := by
  refine Fin.cases ?_ (fun index => ?_) index
  · change (Window.streamBit stream).get (afterReset selection state) =
      (Window.streamBit stream).get state
    unfold Window.streamBit
    split
    · exact congrArg Prod.fst (afterReset_flags selection state flags)
    · exact congrArg (fun controls : Frame.Controls => controls.2.2)
        (afterReset_flags selection state flags)
  · change (Window.addressBit ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩).get
        (afterReset selection state) =
      (Window.addressBit ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩).get state
    simpa only [Window.addressBit_get] using congrArg
      (fun address : Window.Address => address.val.testBit (14 - index.val))
      (afterReset_address selection state)

private lemma enable_flip_pool_congr (first second : Window.Raw)
    (same : first.1.1.1.2 = second.1.1.1.2) :
    (Window.Enable.outputBit.flip first).1.1.1.2 =
      (Window.Enable.outputBit.flip second).1.1.1.2 := by
  let withPool (pool : MAU.Inversion.SharedEEA.Scanned.Pool 256) : Window.Raw :=
    ((((first.1.1.1.1, pool), first.1.1.2), first.1.2), first.2)
  have firstRead : (Window.Enable.outputBit.flip first).1.1.1.2 =
      (Window.Enable.outputBit.flip (withPool first.1.1.1.2)).1.1.1.2 := rfl
  have secondRead : (Window.Enable.outputBit.flip second).1.1.1.2 =
      (Window.Enable.outputBit.flip (withPool second.1.1.1.2)).1.1.1.2 := rfl
  exact firstRead.trans ((congrArg
    (fun pool => (Window.Enable.outputBit.flip (withPool pool)).1.1.1.2) same).trans
      secondRead.symm)

/-- The same paid enable inverse sees the same complete pool after saving and resetting Y. -/
lemma enable_afterReset_pool (selection : Selector) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    (Window.Enable.step stream width bounded (afterReset selection state)).1.1.1.2 =
      (Window.Enable.step stream width bounded state).1.1.1.2 := by
  have sameZero :
      (∀ index, (Window.Enable.digitBit stream width bounded index).get
        (afterReset selection state) = false) ↔
      (∀ index, (Window.Enable.digitBit stream width bounded index).get state = false) := by
    apply forall_congr'
    intro index
    rw [afterReset_digit selection stream width bounded state flags index]
  unfold Window.Enable.step Window.Enable.toggleStep
  change (if ∀ index, (Window.Enable.digitBit stream width bounded index).get
      (afterReset selection state) = false then afterReset selection state
      else Window.Enable.outputBit.flip (afterReset selection state)).1.1.1.2 =
    (if ∀ index, (Window.Enable.digitBit stream width bounded index).get state = false
      then state else Window.Enable.outputBit.flip state).1.1.1.2
  by_cases zero : ∀ index,
      (Window.Enable.digitBit stream width bounded index).get state = false
  · rw [if_pos (sameZero.mpr zero), if_pos zero]
    exact afterReset_pool selection state flags
  · rw [if_neg (fun matched => zero (sameZero.mp matched)), if_neg zero]
    exact enable_flip_pool_congr _ _ (afterReset_pool selection state flags)

private lemma prepare_pool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    (Control.prepareStep stream width bounded state).1.1.1.2 =
      (Window.Enable.step stream width bounded state).1.1.1.2 := by
  unfold Control.prepareStep Control.copyStep EncodedBit.cnotStep
  split
  · rw [Control.toggle_normal_comm]
    rfl
  · rfl

/-- The real F-to-N preparation has the same pool after the physical save and reset. -/
lemma prepare_afterReset_pool (selection : Selector) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false) :
    (Control.prepareStep stream width bounded (afterReset selection state)).1.1.1.2 =
      (Control.prepareStep stream width bounded state).1.1.1.2 :=
  (prepare_pool stream width bounded (afterReset selection state)).trans
    ((enable_afterReset_pool selection stream width bounded state flags).trans
      (prepare_pool stream width bounded state).symm)

/-- Division reuses its original actual temporary-control clean-pool boundary. -/
lemma prepare_afterReset_cleanPool (selection : Selector) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Control.prepareStep stream width bounded state).1) :
    Frame.CleanPool
      (Control.prepareStep stream width bounded (afterReset selection state)).1 :=
  (prepare_afterReset_pool selection stream width bounded state flags).trans clean

/-- The original actual enable inverse supplies the clean-pool boundary after Save and reset. -/
lemma enable_afterReset_cleanPool (selection : Selector) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw)
    (flags : ((Placement.layout Save.ports).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Save.ports).grouping state.1).1.2.2 = false)
    (clean : Frame.CleanPool (Window.Enable.step stream width bounded state).1) :
    Frame.CleanPool
      (Window.Enable.step stream width bounded (afterReset selection state)).1 :=
  (enable_afterReset_pool selection stream width bounded state flags).trans clean

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
