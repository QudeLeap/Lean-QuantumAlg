/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Boundary
import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Inactive.Tail

/-!
# Actual saved/reset multiplication labels at the reused forward boundary

Save uses the original denominator before inversion. The genuine N flag
survives the actual F clearing, physical Y reset, reused forward and its
later own adjoint. No full-source or clean-pool equation is supplied as a
caller callback; these are derived from the actual initialized label and
the actual save/reset coordinate laws.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma initial_source_independent (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (first second : Fin (2 ^ modulus.size)) (pool otherPool : Pool modulus.size)
    (flags otherFlags : ControlledResidentFrame.Flags) :
    (ControlledResident.initial modulus input first pool flags).1.1.1 =
      (ControlledResident.initial modulus input second otherPool otherFlags).1.1.1 := rfl

private lemma enable_numerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Frame.numerator (Window.Enable.step stream width bounded state).1 =
      Frame.numerator state.1 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have retained := Window.Enable.step_other stream width bounded
    ((Window.resultWord .numerator).bit index) (by
      intro same
      have position := congrArg Fin.val same
      rw [Window.Enable.outputBit_wire, Window.resultWord_wire] at position
      change 560 = 580 + (255 - index.val) at position
      have within := index.isLt
      omega) state
  exact (WordPort.bit_get .numerator index
    (Window.Enable.step stream width bounded state).1).symm.trans
      (retained.trans (WordPort.bit_get .numerator index state.1))

private lemma enable_arithmeticFlags (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (assignment : PortAssignment) (state : Window.Raw) (clean : Frame.CleanPool state.1) :
    ((Placement.layout assignment).grouping
      (Window.Enable.step stream width bounded state).1).1.1.2 = false ∧
    ((Placement.layout assignment).grouping
      (Window.Enable.step stream width bounded state).1).1.2.1 = false ∧
    ((Placement.layout assignment).grouping
      (Window.Enable.step stream width bounded state).1).1.2.2 = false := by
  have flags := Placement.grouping_flags_clean assignment state.1 clean
  have retained (index : Fin 3) :
      (Placement.arithmeticFlagPort assignment index).get
          ((Placement.layout assignment).grouping
            (Window.Enable.step stream width bounded state).1) =
        (Placement.arithmeticFlagPort assignment index).get
          ((Placement.layout assignment).grouping state.1) := by
    have read := Window.Enable.step_other stream width bounded
      (Window.pointBit (arithmeticFlag index)) (by
        intro same
        have position := congrArg Fin.val same
        rw [Window.Enable.outputBit_wire, Window.pointBit_wire, arithmeticFlag_wire] at position
        unfold arithmeticFlagIndex at position
        split_ifs at position <;> omega) state
    exact (Placement.arithmeticFlagPort_get assignment index _).trans
      (read.trans (Placement.arithmeticFlagPort_get assignment index state.1).symm)
  exact ⟨(retained 0).trans flags.1, (retained 1).trans flags.2.1,
    (retained 2).trans flags.2.2⟩

private lemma initial_clean_pool (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) :
    Frame.CleanPool (Inversion.initial input numerator (0, (0, false)) flags) :=
  Inversion.transport_clean_pool Inversion.modulus_size _
    (ControlledResident.initial_pool modulus input numerator (0, (0, false)) flags)

private lemma initial_physical_label (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) :
    Inversion.initial input numerator (0, (0, false)) flags =
      Inversion.Transport.state Inversion.modulus_size
        (ControlledResident.initial modulus input numerator (0, (0, false)) flags) := rfl

/-- The real live-F multiplication input retains the original initialized denominator source. -/
def activeMultiplicationInitial (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  Window.Enable.step stream width widthBound (clearedInitial input numerator flags address)

/-- The actual whole-pool clearing following Save and physical Y reset. -/
def activeMultiplicationClearedReset (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  Window.Enable.step stream width widthBound (afterReset .normal
    (activeMultiplicationInitial stream width widthBound input numerator flags address))

/-- Complete result of the actual reused forward, with the live F restored on the same digit. -/
def activeMultiplicationAfterForward (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) : Window.Raw :=
  let candidate := activeMultiplicationClearedReset stream width widthBound input numerator
    flags address
  Window.Enable.step stream width widthBound
    (Inversion.Transport.state Inversion.modulus_size
      (ControlledResidentReuse.result modulus input positive bounded
        (Boundary.savedWord candidate.1) (Boundary.source candidate.1).1.1.2
          (Boundary.source candidate.1).2), candidate.2)

attribute [local irreducible] modulus Boundary.sourceAt afterReset Inversion.initial

lemma activeMultiplicationInitial_flags (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    ((Placement.layout Save.ports).grouping
      (activeMultiplicationInitial stream width widthBound input numerator flags address).1).1.1.2 =
        false ∧
    ((Placement.layout Save.ports).grouping
      (activeMultiplicationInitial stream width widthBound input numerator flags address).1).1.2.1 =
        false ∧
    ((Placement.layout Save.ports).grouping
      (activeMultiplicationInitial stream width widthBound input numerator flags address).1).1.2.2 =
        false :=
  enable_arithmeticFlags stream width widthBound Save.ports
    (clearedInitial input numerator flags address) (initial_clean_pool input numerator flags)

/-- Actual complete original-source reads establish the reused forward's initialized boundary. -/
lemma multiplication_savedReset_retained (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size))
    (outsideA : modulus.size ≤ observed.wire.val) :
    observed.get (Boundary.source
      (activeMultiplicationClearedReset stream width widthBound input numerator
        flags address).1).1.1.1 =
      observed.get (ControlledResident.initial modulus input 0
        (Boundary.source (activeMultiplicationClearedReset stream width widthBound input
          numerator flags address).1).1.1.2
        (Boundary.source (activeMultiplicationClearedReset stream width widthBound input
          numerator flags address).1).2).1.1.1 := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  have arithmeticFlags := activeMultiplicationInitial_flags stream width widthBound input numerator
    flags address
  have cleared := sourceAt_source_eq (width := modulus.size) Inversion.modulus_size
    (activeMultiplicationClearedReset stream width widthBound input numerator flags address).1
    (afterReset .normal original).1
    (enable_source stream width widthBound (afterReset .normal original))
  have enabled := sourceAt_source_eq (width := modulus.size) Inversion.modulus_size original.1
    (clearedInitial input numerator flags address).1
    (enable_source stream width widthBound (clearedInitial input numerator flags address))
  have originalInitial := (congrArg (Boundary.sourceAt Inversion.modulus_size)
    (initial_physical_label input numerator flags)).trans
      (sourceAt_transport Inversion.modulus_size
        (ControlledResident.initial modulus input numerator (0, (0, false)) flags))
  have initialSource := initial_source_independent modulus input numerator 0 (0, (0, false))
    (Boundary.source (activeMultiplicationClearedReset stream width widthBound input numerator
      flags address).1).1.1.2 flags
    (Boundary.source (activeMultiplicationClearedReset stream width widthBound input numerator
      flags address).1).2
  exact (congrArg (fun source => observed.get source) cleared).trans
    ((afterReset_source_typed .normal original arithmeticFlags observed outsideA).trans
      ((congrArg (fun source => observed.get source) enabled).trans
        ((congrArg (fun state : ControlledResidentFrame.Data modulus.size =>
          observed.get state.1.1.1) originalInitial).trans
            (congrArg (fun source => observed.get source) initialSource))))

/-- The actual second call's post-reset forward starts from the genuine initialized history. -/
lemma multiplication_savedReset_forward (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (selected : flags.2.1 = true) (address : Window.Address) :
    (residentWithNormal stream width widthBound Boundary.reusedForward).applyNormalized
        environment (Window.ket (afterReset .normal
          (activeMultiplicationInitial stream width widthBound input numerator flags address))) =
      Window.ket (activeMultiplicationAfterForward stream width widthBound input positive bounded
        numerator flags address) := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  let candidate := activeMultiplicationClearedReset stream width widthBound input numerator
    flags address
  have arithmeticFlags := activeMultiplicationInitial_flags stream width widthBound input numerator
    flags address
  have cleared := Window.Enable.step_step stream width widthBound
    (clearedInitial input numerator flags address)
  have beforePool : Frame.CleanPool (Window.Enable.step stream width widthBound original).1 :=
    (congrArg (fun state : Window.Raw => state.1.1.1.2) cleared).trans
      (initial_clean_pool input numerator flags)
  have candidatePool : Frame.CleanPool candidate.1 :=
    enable_afterReset_cleanPool .normal stream width widthBound original arithmeticFlags
      beforePool
  have initialFlags : (clearedInitial input numerator flags address).1.2 = flags :=
    (congrArg (fun state : Frame.Raw => state.2)
      (initial_physical_label input numerator flags)).trans
      ((Inversion.Transport.state_flags Inversion.modulus_size
        (ControlledResident.initial modulus input numerator (0, (0, false)) flags)).trans
          (ControlledResident.initial_flags modulus input numerator (0, (0, false)) flags))
  have beforeNormal : Window.normalBit.get original = true :=
    (clear_normal stream width widthBound (clearedInitial input numerator flags address)).trans
      ((congrArg (fun values : Frame.Controls => values.2.1) initialFlags).trans selected)
  have candidateNormal : Window.normalBit.get candidate = true :=
    (clear_normal stream width widthBound (afterReset .normal original)).trans
      ((afterReset_selector .normal .normal original arithmeticFlags).trans beforeNormal)
  have candidateReset : Frame.numerator candidate.1 = Horner.zeroWord :=
    (enable_numerator stream width widthBound (afterReset .normal original)).trans
      (afterReset_numerator .normal original)
  have actual := Boundary.reusedForward_saved_reset environment input coprime positive bounded
    candidate.1 (multiplication_savedReset_retained stream width widthBound input numerator
      flags address)
    (sourceAt_reset (width := modulus.size) Inversion.modulus_size candidate.1 candidateReset)
    (sourceAt_clean (width := modulus.size) Inversion.modulus_size candidate.1 candidatePool)
    (sourceAt_normal (width := modulus.size) Inversion.modulus_size candidate.1 candidateNormal)
  exact residentWithNormal_apply stream width widthBound Boundary.reusedForward environment
    (afterReset .normal original) _ actual

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
