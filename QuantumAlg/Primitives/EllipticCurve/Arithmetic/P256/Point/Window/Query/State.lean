/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Readout

/-!
# Complete query-arithmetic coordinates from the actual initialized pool

The actual enable can set its original output at560. It preserves the
three real native flags at559,569,579. Those flags, rather than an
incorrect zero-entire-pool premise after computing the enable, supply
the complete native arithmetic coordinates. Every original source and
saved address bit remains in that same exact full label.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

private lemma sourceState_scan_get (stream : Fin 2)
    (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256)) (state : Raw) :
    (Frame.scanBit bit).get (sourceState stream state) = (Frame.scanBit bit).get state.1 := by
  unfold sourceState
  rw [streamPlacement_grouping]
  split <;> rfl

private lemma sourceState_flag_get (stream : Fin 2) (index : Fin 3) (state : Raw) :
    (arithmeticFlag index).get (sourceState stream state) =
      (arithmeticFlag index).get state.1 := by
  unfold arithmeticFlag
  split_ifs <;> exact sourceState_scan_get stream _ state

lemma enable_flag_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin 3) (state : Raw) :
    (arithmeticFlag index).get (Enable.step stream width bounded state).1 =
      (arithmeticFlag index).get state.1 := by
  apply Enable.step_other stream width bounded (pointBit (arithmeticFlag index))
  intro same
  have positions := congrArg Fin.val same
  rw [Enable.outputBit_wire, pointBit_wire, arithmeticFlag_wire] at positions
  unfold arithmeticFlagIndex at positions
  split_ifs at positions <;> omega

/-- The real enable leaves all fifteen original address bits in their complete original word. -/
lemma enable_address (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    (Enable.step stream width bounded state).2 = state.2 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have reversed : 14 - index.rev.val = index.val := by
    rw [Fin.val_rev]
    have within := index.isLt
    omega
  have actual := enable_address_get stream width bounded index.rev state
  simpa only [addressBit_get, reversed] using actual

/-- This is a mathematical readout of the actual source roles after the real enable executes. -/
def arithmeticSource (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    Frame.Raw := sourceState stream (Enable.step stream width bounded state)

lemma arithmeticSource_flags (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).1.1.2 =
      false ∧
    ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).1.2.1 =
      false ∧
    ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).1.2.2 =
      false := by
  have original := Frame.arithmetic_flags_clean state.1 clean
  have zeros (index : Fin 3) :
      (arithmeticFlag index).get (arithmeticSource stream width bounded state) = false := by
    rw [arithmeticSource, sourceState_flag_get, enable_flag_get]
    fin_cases index
    · exact original.1
    · exact original.2.1
    · exact original.2.2
  exact ⟨(Placement.arithmeticFlagPort_get ports ⟨0, by decide⟩ _).trans (zeros 0),
    (Placement.arithmeticFlagPort_get ports ⟨1, by decide⟩ _).trans (zeros 1),
    (Placement.arithmeticFlagPort_get ports ⟨2, by decide⟩ _).trans (zeros 2)⟩

/-- The actual original pool supplies all native coordinates, including an arbitrary old address. -/
lemma state_eq_arithmeticInput (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    state = arithmeticInput stream width bounded ports
      (ports.source.value (arithmeticSource stream width bounded state))
      (ports.target.value (arithmeticSource stream width bounded state))
      (ports.multiplier.value (arithmeticSource stream width bounded state))
      ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2
      state.2 := by
  have native := Native.state_eq_arithmeticState_of_flags ports
    (arithmeticSource stream width bounded state)
    (arithmeticSource_flags stream width bounded ports state clean)
  have covered : Enable.step stream width bounded state =
      streamInput stream
        (Native.arithmeticState ports
          (ports.source.value (arithmeticSource stream width bounded state))
          (ports.target.value (arithmeticSource stream width bounded state))
          (ports.multiplier.value (arithmeticSource stream width bounded state))
          ((Placement.layout ports).grouping (arithmeticSource stream width bounded state)).2.2)
        state.2 :=
    (streamInput_sourceState stream (Enable.step stream width bounded state)).symm.trans
      (congrArg₂ (streamInput stream) native (enable_address stream width bounded state))
  exact (Enable.step_step stream width bounded state).symm.trans
    (congrArg (Enable.step stream width bounded) covered)

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
