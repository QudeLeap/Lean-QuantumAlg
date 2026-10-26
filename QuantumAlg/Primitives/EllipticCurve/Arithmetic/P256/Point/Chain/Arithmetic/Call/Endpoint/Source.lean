/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Prepare

/-!
# Original source retention in the complete division output

The inverse reuse grouping is read at each certified original source bit.
Every bit outside the A payload agrees with the whole original initialized
source, including X padding, lengths, flags and retained history.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma reusedInitial_source_read (modulus : Nat)
    (input saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size))
    (outside : modulus.size ≤ observed.wire.val) :
    observed.get (ControlledResidentReuse.initial modulus input saved pool flags).1.1.1 =
      observed.get (ControlledResident.initial modulus input 0 pool flags).1.1.1 := by
  let state := ControlledResidentReuse.initial modulus input saved pool flags
  have grouped : (WorkspaceReuse.placement modulus.size).grouping state.1 =
      (ControlledResident.initial modulus input saved pool flags).1 :=
    congrArg (fun value : ControlledResidentFrame.Data modulus.size => value.1)
      ((ControlledResidentReuse.layout modulus.size).grouping.apply_symm_apply
        (ControlledResident.initial modulus input saved pool flags))
  have read := WorkspaceReuse.grouping_original_read modulus.size state.1 observed outside
  have sourceRead := congrArg
    (fun value : OutputCopy.Data modulus.size => observed.get value.1.1) grouped
  have independent := initial_source_independent modulus input saved 0 pool pool flags flags
  exact read.symm.trans (sourceRead.trans
    (congrArg (fun value => observed.get value) independent))

attribute [local irreducible] modulus Inversion.initial Swap.step

/-- Outside saved A, every original source read is restored by the actual adjoint. -/
lemma division_afterBackward_source (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size))
    (outside : modulus.size ≤ observed.wire.val) :
    observed.get (Boundary.source
      (activeDivisionAfterBackward stream width widthBound input positive bounded numerator
        flags address).1).1.1.1 =
      observed.get (ControlledResident.initial modulus input 0 (0, (0, false)) flags).1.1.1 := by
  let candidate := activeDivisionClearedReset stream width widthBound input positive bounded
    numerator flags address
  let initial := ControlledResidentReuse.initial modulus input (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
  have restored := restore_source stream width widthBound
    (Inversion.Transport.state Inversion.modulus_size initial, candidate.2)
  have source := sourceAt_source_eq Inversion.modulus_size
    (activeDivisionAfterBackward stream width widthBound input positive bounded numerator
      flags address).1 (Inversion.Transport.state Inversion.modulus_size initial) restored
  have transported := sourceAt_transport Inversion.modulus_size initial
  have sameSource := source.trans
    (congrArg (fun state : ControlledResidentFrame.Data modulus.size => state.1.1.1) transported)
  have reused := reusedInitial_source_read modulus input (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2 observed outside
  have independent := initial_source_independent modulus input 0 0
    (Boundary.source candidate.1).1.1.2 (0, (0, false)) (Boundary.source candidate.1).2 flags
  exact (congrArg (fun value => observed.get value) sameSource).trans
    (reused.trans (congrArg (fun value => observed.get value) independent))

private lemma original_source_read (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding modulus.size)) :
    observed.get (Boundary.source
      (activeDivisionInitial stream width widthBound input numerator flags address).1).1.1.1 =
      observed.get (ControlledResident.initial modulus input 0 (0, (0, false)) flags).1.1.1 := by
  have restored := restore_source stream width widthBound
    (clearedInitial input numerator flags address)
  have source := sourceAt_source_eq Inversion.modulus_size
    (activeDivisionInitial stream width widthBound input numerator flags address).1
    (clearedInitial input numerator flags address).1 restored
  have initial := (congrArg (Boundary.sourceAt Inversion.modulus_size)
    (initial_physical_label input numerator flags)).trans
      (sourceAt_transport Inversion.modulus_size
        (ControlledResident.initial modulus input numerator (0, (0, false)) flags))
  exact (congrArg (fun value => observed.get value) source).trans
    ((congrArg (fun value : ControlledResidentFrame.Data modulus.size =>
      observed.get value.1.1.1) initial).trans
        (congrArg (fun value => observed.get value)
          (initial_source_independent modulus input numerator 0 (0, (0, false))
            (0, (0, false)) flags flags)))

private lemma sourceAt_read_refl (state : Frame.Raw)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding 256)) :
    observed.get (Boundary.sourceAt rfl state).1.1.1 = observed.get state.1.1.1 := rfl

private lemma source_width : (MAU.Inversion.SharedEEA.encoding 256).width = 559 := by
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

private lemma swap_source_read {width : Nat} (same : width = 256) (state : Window.Raw)
    (observed : EncodedBit (MAU.Inversion.SharedEEA.encoding width))
    (outside : width ≤ observed.wire.val) :
    observed.get (Boundary.sourceAt same (Swap.step state).1).1.1.1 =
      observed.get (Boundary.sourceAt same state.1).1.1.1 := by
  cases same
  let bit := Frame.scanBit
    (BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding 256)
      (poolEncoding 256) observed)
  have bound : observed.wire.val < 559 := by
    simpa only [source_width] using observed.wire.isLt
  have physical := swap_pointBit_outside bit outside
    (Or.inl (by change observed.wire.val < 580; omega)) state
  have bitRead (value : Frame.Raw) : bit.get value = observed.get value.1.1.1 := rfl
  exact (sourceAt_read_refl (Swap.step state).1 observed).trans
    ((bitRead (Swap.step state).1).symm.trans
      (physical.trans ((bitRead state.1).trans (sourceAt_read_refl state.1 observed).symm)))

private lemma source_eq_of_reads {width : Nat} (same : width = 256)
    (first second : Window.Raw) (work1 : Frame.work1 first.1 = Frame.work1 second.1)
    (outside : ∀ observed : EncodedBit (MAU.Inversion.SharedEEA.encoding width),
      width ≤ observed.wire.val →
        observed.get (Boundary.sourceAt same first.1).1.1.1 =
          observed.get (Boundary.sourceAt same second.1).1.1.1) :
    first.1.1.1.1 = second.1.1.1.1 := by
  cases same
  apply EncodedBit.state_eq_of_get_eq (MAU.Inversion.SharedEEA.encoding_surjective 256)
  intro observed
  by_cases inside : observed.wire.val < 256
  · let bit := Frame.scanBit
      (BinaryLabelEncoding.prodLeftBit (MAU.Inversion.SharedEEA.encoding 256)
        (poolEncoding 256) observed)
    exact work1_eq_get first second work1 bit inside
  · exact outside observed (Nat.le_of_not_gt inside)

/-- The real final swap restores the whole original source, not just numerical X and A. -/
lemma division_active_source (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    (Swap.step (activeDivisionAfterBackward stream width widthBound input positive bounded
      numerator flags address)).1.1.1.1 =
      (activeDivisionInitial stream width widthBound input numerator flags address).1.1.1.1 := by
  have words := division_afterBackward_words stream width widthBound input positive bounded
    numerator flags address
  have initialZero := (restore_word .work1 stream width widthBound
    (clearedInitial input numerator flags address)).trans (initial_work1_zero input numerator flags)
  apply source_eq_of_reads Inversion.modulus_size
  · exact ((Swap.step_work1 _).trans words.2.1).trans initialZero.symm
  · intro observed outside
    exact (swap_source_read Inversion.modulus_size _ observed outside).trans
      ((division_afterBackward_source stream width widthBound input positive bounded numerator
        flags address observed outside).trans
          (original_source_read stream width widthBound input numerator flags address
            observed).symm)

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
