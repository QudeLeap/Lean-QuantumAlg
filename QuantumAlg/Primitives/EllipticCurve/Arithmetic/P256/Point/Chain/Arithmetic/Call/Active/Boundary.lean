/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active
import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Inactive.Tail
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Boundary.Initial

/-!
# Actual saved/reset division labels at the same-program adjoint boundary

Every retained source bit, including the original three tail systems and
all small history, is transported from the complete real forward result.
The Y-zero premise is supplied only after physical reset. Clearing F and
the temporary N transfer remain part of the same executed resident wrapper.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma sourceAt_source_eq {width : Nat} (same : width = 256)
    (first second : Frame.Raw) (retained : first.1.1.1 = second.1.1.1) :
    (Boundary.sourceAt same first).1.1.1 = (Boundary.sourceAt same second).1.1.1 := by
  cases same
  exact retained

private lemma sourceAt_transport {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) :
    Boundary.sourceAt same (Inversion.Transport.state same state) = state := by
  cases same
  rfl

private lemma sourceAt_reset {width : Nat} (same : width = 256) (state : Frame.Raw)
    (reset : Frame.numerator state = Horner.zeroWord) :
    (Boundary.sourceAt same state).1.2 = 0 := by
  cases same
  exact reset

private lemma sourceAt_clean {width : Nat} (same : width = 256) (state : Frame.Raw)
    (clean : Frame.CleanPool state) :
    (Boundary.sourceAt same state).1.1.2 = (0, (0, false)) := by
  cases same
  exact clean

private lemma sourceAt_normal {width : Nat} (same : width = 256) (state : Frame.Raw)
    (normal : state.2.2.1 = true) :
    (Boundary.sourceAt same state).2.2.1 = true := by
  cases same
  exact normal

private lemma result_source_independent (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (first second : Fin (2 ^ modulus.size)) (pool otherPool : Pool modulus.size)
    (flags otherFlags : ControlledResidentFrame.Flags) :
    (ControlledResident.result modulus input positive bounded first pool flags).1.1.1 =
      (ControlledResident.result modulus input positive bounded second otherPool
        otherFlags).1.1.1 :=
  rfl

private lemma restore_source (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    (Control.restoreStep stream width bounded state).1.1.1.1 = state.1.1.1.1 :=
  (prepare_source stream width bounded (Control.restoreStep stream width bounded state)).symm.trans
    (congrArg (fun value : Window.Raw => value.1.1.1.1)
      (prepare_restore stream width bounded state))

private lemma prepare_numerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Frame.numerator (Control.prepareStep stream width bounded state).1 =
      Frame.numerator state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have retained := Control.prepare_other stream width bounded
    ((Window.resultWord .numerator).bit index) (by
      intro same
      have position := congrArg Fin.val same
      rw [Window.Enable.outputBit_wire, Window.resultWord_wire] at position
      change 560 = 580 + (255 - index.val) at position
      have within := index.isLt
      omega) (by
      intro same
      have position := congrArg Fin.val same
      rw [Window.normalBit_wire, Window.resultWord_wire] at position
      change 837 = 580 + (255 - index.val) at position
      have within := index.isLt
      omega) state
  exact (WordPort.bit_get .numerator index
    (Control.prepareStep stream width bounded state).1).symm.trans
      (retained.trans (WordPort.bit_get .numerator index state.1))

private lemma restore_arithmeticFlags (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (assignment : PortAssignment) (state : Window.Raw) (clean : Frame.CleanPool state.1) :
    ((Placement.layout assignment).grouping
      (Control.restoreStep stream width bounded state).1).1.1.2 = false ∧
    ((Placement.layout assignment).grouping
      (Control.restoreStep stream width bounded state).1).1.2.1 = false ∧
    ((Placement.layout assignment).grouping
      (Control.restoreStep stream width bounded state).1).1.2.2 = false := by
  have flags := Placement.grouping_flags_clean assignment state.1 clean
  have retained (index : Fin 3) :
      (Placement.arithmeticFlagPort assignment index).get
          ((Placement.layout assignment).grouping
            (Control.restoreStep stream width bounded state).1) =
        (Placement.arithmeticFlagPort assignment index).get
          ((Placement.layout assignment).grouping state.1) := by
    have read := Control.restore_other stream width bounded
      (Window.pointBit (arithmeticFlag index)) (by
        intro same
        have position := congrArg Fin.val same
        rw [Window.Enable.outputBit_wire, Window.pointBit_wire, arithmeticFlag_wire] at position
        unfold arithmeticFlagIndex at position
        split_ifs at position <;> omega) (by
        intro same
        have position := congrArg Fin.val same
        rw [Window.normalBit_wire, Window.pointBit_wire, arithmeticFlag_wire] at position
        unfold arithmeticFlagIndex at position
        split_ifs at position <;> omega) state
    exact (Placement.arithmeticFlagPort_get assignment index _).trans
      (read.trans (Placement.arithmeticFlagPort_get assignment index state.1).symm)
  exact ⟨(retained 0).trans flags.1, (retained 1).trans flags.2.1,
    (retained 2).trans flags.2.2⟩

attribute [local irreducible] Inversion.result modulus

/-- The actual forward result and paid control restoration supply the real save's three flags. -/
lemma activeDivisionAfterForward_flags (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    ((Placement.layout Save.ports).grouping
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1).1.1.2 = false ∧
    ((Placement.layout Save.ports).grouping
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1).1.2.1 = false ∧
    ((Placement.layout Save.ports).grouping
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1).1.2.2 = false :=
  restore_arithmeticFlags stream width widthBound Save.ports
    (clearedResult input positive bounded numerator flags address)
    (Inversion.result_clean_pool input positive bounded numerator (0, (0, false)) flags
      rfl rfl rfl)

/-- The real first save/reset label is followed by the actual temporary-control preparation. -/
def activeDivisionClearedReset (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  Control.prepareStep stream width widthBound (afterReset .enable
    (activeDivisionAfterForward stream width widthBound input positive bounded
      numerator flags address))

/-- Complete output of the actual reused adjoint and paid temporary-control restoration. -/
def activeDivisionAfterBackward (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let candidate := activeDivisionClearedReset stream width widthBound input positive bounded
    numerator flags address
  Control.restoreStep stream width widthBound
    (Inversion.Transport.state Inversion.modulus_size
      (ControlledResidentReuse.initial modulus input (Boundary.savedWord candidate.1)
        (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2), candidate.2)

section

attribute [local irreducible] Boundary.sourceAt afterReset

/-- Actual source reads discharge the complete reused-adjoint boundary, not just word values. -/
lemma division_savedReset_retained (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address)
    (arithmeticFlags :
      ((Placement.layout Save.ports).grouping
        (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address).1).1.1.2 = false ∧
      ((Placement.layout Save.ports).grouping
        (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address).1).1.2.1 = false ∧
      ((Placement.layout Save.ports).grouping
        (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address).1).1.2.2 = false)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size))
    (outsideA : modulus.size ≤ observed.wire.val) :
    observed.get (Boundary.source
      (activeDivisionClearedReset stream width widthBound input positive bounded
        numerator flags address).1).1.1.1 =
      observed.get (ControlledResident.result modulus input positive bounded 0
        (Boundary.source (activeDivisionClearedReset stream width widthBound input
          positive bounded numerator flags address).1).1.1.2
        (Boundary.source (activeDivisionClearedReset stream width widthBound input
          positive bounded numerator flags address).1).2).1.1.1 := by
  let original := activeDivisionAfterForward stream width widthBound input positive bounded
    numerator flags address
  have prepared := sourceAt_source_eq (width := modulus.size) Inversion.modulus_size
    (activeDivisionClearedReset stream width widthBound input positive bounded
      numerator flags address).1 (afterReset .enable original).1
    (prepare_source stream width widthBound (afterReset .enable original))
  have restored := sourceAt_source_eq (width := modulus.size) Inversion.modulus_size original.1
    (clearedResult input positive bounded numerator flags address).1
    (restore_source stream width widthBound
      (clearedResult input positive bounded numerator flags address))
  have physicalResult : (clearedResult input positive bounded numerator flags address).1 =
      Inversion.Transport.state Inversion.modulus_size
        (ControlledResident.result modulus input positive bounded numerator (0, (0, false))
          flags) := by
    unfold clearedResult Inversion.result
    rfl
  have originalResult := (congrArg (Boundary.sourceAt Inversion.modulus_size) physicalResult).trans
    (sourceAt_transport Inversion.modulus_size
      (ControlledResident.result modulus input positive bounded numerator (0, (0, false)) flags))
  have resultSource := result_source_independent modulus input positive bounded numerator 0
    (0, (0, false))
    (Boundary.source (activeDivisionClearedReset stream width widthBound input positive bounded
      numerator flags address).1).1.1.2 flags
    (Boundary.source (activeDivisionClearedReset stream width widthBound input positive bounded
      numerator flags address).1).2
  exact (congrArg (fun source => observed.get source) prepared).trans
    ((afterReset_source_typed .enable original arithmeticFlags observed outsideA).trans
      ((congrArg (fun source => observed.get source) restored).trans
        ((congrArg (fun state : ControlledResidentFrame.Data modulus.size =>
          observed.get state.1.1.1) originalResult).trans
            (congrArg (fun source => observed.get source) resultSource))))

/-- The actual post-reset resident segment reaches its complete restored initial source. -/
lemma division_savedReset_backward (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (selected : flags.2.1 = true) (address : Window.Address) :
    (residentWithTemporary stream width widthBound Boundary.reusedBackward).applyNormalized
        environment (Window.ket (afterReset .enable
          (activeDivisionAfterForward stream width widthBound input positive bounded
            numerator flags address))) =
      Window.ket (activeDivisionAfterBackward stream width widthBound input positive bounded
        numerator flags address) := by
  let original := activeDivisionAfterForward stream width widthBound input positive bounded
    numerator flags address
  let candidate := activeDivisionClearedReset stream width widthBound input positive bounded
    numerator flags address
  have arithmeticFlags := activeDivisionAfterForward_flags stream width widthBound input positive
    bounded numerator flags address
  have prepared := prepare_restore stream width widthBound
    (clearedResult input positive bounded numerator flags address)
  have beforePool : Frame.CleanPool (Control.prepareStep stream width widthBound original).1 :=
    (congrArg (fun state : Window.Raw => state.1.1.1.2) prepared).trans
      (Inversion.result_clean_pool input positive bounded numerator (0, (0, false)) flags
        rfl rfl rfl)
  have candidatePool : Frame.CleanPool candidate.1 :=
    prepare_afterReset_cleanPool .enable stream width widthBound original arithmeticFlags beforePool
  have beforeNormal : Window.normalBit.get
      (Control.prepareStep stream width widthBound original) = true :=
    (congrArg (fun state : Window.Raw => Window.normalBit.get state) prepared).trans
      ((congrArg (fun values : Frame.Controls => values.2.1)
        (Inversion.result_flags input positive bounded numerator (0, (0, false)) flags)).trans
          selected)
  have sameNormal : Window.normalBit.get (afterReset .enable original) =
      Window.normalBit.get original :=
    afterReset_selector .enable .normal original arithmeticFlags
  have sameFlag : Window.Enable.outputBit.get (afterReset .enable original) =
      Window.Enable.outputBit.get original :=
    afterReset_selector .enable .enable original arithmeticFlags
  have candidateNormal : Window.normalBit.get candidate = true :=
    (temporary_normal stream width widthBound (afterReset .enable original)).trans
      ((congrArg₂ Bool.xor sameNormal sameFlag).trans
        ((temporary_normal stream width widthBound original).symm.trans beforeNormal))
  have candidateReset : Frame.numerator candidate.1 = Horner.zeroWord :=
    (prepare_numerator stream width widthBound (afterReset .enable original)).trans
      (afterReset_numerator .enable original)
  have actual := Boundary.reusedBackward_saved_reset environment input coprime positive bounded
    candidate.1 (division_savedReset_retained stream width widthBound input positive bounded
      numerator flags address arithmeticFlags)
    (sourceAt_reset (width := modulus.size) Inversion.modulus_size candidate.1 candidateReset)
    (sourceAt_clean (width := modulus.size) Inversion.modulus_size candidate.1 candidatePool)
    (sourceAt_normal (width := modulus.size) Inversion.modulus_size candidate.1 candidateNormal)
  exact residentWithTemporary_apply stream width widthBound Boundary.reusedBackward environment
    (afterReset .enable original) _ actual

end

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
