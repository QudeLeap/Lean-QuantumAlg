/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Program
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Source
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag.Action

/-!
# Complete remainder arithmetic in the identical aligned physical source frame

Identical source wires identify every complete focused action. In
particular both native additions have the original full remainder
semantics after alignment, with every complement and pool bit retained.
The actual runtime address, guard and alignment cleanup are separate
executed instructions, not supplied by this static coordinate theorem.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderCoordinates

noncomputable section

open EncodedBit

private lemma pool_onto (width : Nat) : Function.Surjective (poolEncoding width).encode :=
  Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective
    (Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective Scanned.bool_total)

private lemma conjugate_output {Original Prepared : Type} (coordinates : Original ≃ Prepared)
    (middle : Prepared) (output : Original) (same : coordinates.symm middle = output) :
    middle = coordinates output :=
  (coordinates.apply_symm_apply middle).symm.trans (congrArg coordinates same)

private lemma compose_output {Source Middle Target : Type}
    {source : BinaryLabelEncoding Source} {middle : BinaryLabelEncoding Middle}
    {target : BinaryLabelEncoding Target} (inner : FullPlacement source middle)
    (outer : FullPlacement middle target) (action : Source → Source) (state output : Target)
    (same : (inner.compose outer).step action state = output) :
    inner.step action (outer.grouping state) = outer.grouping output := by
  change outer.grouping.symm (inner.step action (outer.grouping state)) = output at same
  exact conjugate_output outer.grouping _ _ same

/-- Any full overflow action has the identical original semantics beside the entire pool. -/
lemma frame_action {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (action : Addition.TTK.OverflowRegisters window.length →
      Addition.TTK.OverflowRegisters window.length) (state : Data width) :
    (templateFrame window).step (fun pair => (action pair.1, pair.2)) state =
      ((ArithmeticWindowPlacement.placement window).step
        (fun pair => (action pair.1, pair.2)) state.1, state.2) := by
  have equality := (templateFrame window).step_eq_of_source_wires (originalFrame window)
    (ArithmeticTop.overflow_onto window.length) Function.surjective_id
    (Scanned.product_total _ _ (ArithmeticWindowEncoding.complement_surjective window)
      (pool_onto width)) (Scanned.encoding_surjective width) (source_positions window) action state
  exact equality.trans (FullPlacement.retainRight_step
    (ArithmeticWindowPlacement.placement window) (poolEncoding width) action state)

/-- Both actual work words enter the template in the complete preparation of the original result. -/
lemma aligned_action {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (state : Data width) :
    ((ArithmeticTop.placement width window.length (fits window)).full
      (ArithmeticTop.overflow_onto window.length) (Scanned.encoding_surjective width)).step
        (fun pair => (ArithmeticWindowProgram.focusStep operation pair.1, pair.2))
          ((ArithmeticAlignment.Fixed.frame width window.below).grouping state) =
      (ArithmeticAlignment.Fixed.frame width window.below).grouping
        (ArithmeticWindowProgram.step window operation state.1, state.2) := by
  exact compose_output
    ((ArithmeticTop.placement width window.length (fits window)).full
      (ArithmeticTop.overflow_onto window.length) (Scanned.encoding_surjective width))
    (ArithmeticAlignment.Fixed.frame width window.below)
    (fun pair => (ArithmeticWindowProgram.focusStep operation pair.1, pair.2)) state
    (ArithmeticWindowProgram.step window operation state.1, state.2)
    (frame_action window (ArithmeticWindowProgram.focusStep operation) state)

private lemma low_action (width length : Nat) (fits : length ≤ width + 3) (state : Data width) :
    ((ArithmeticTop.placement width length fits).full (ArithmeticTop.overflow_onto length)
        (Scanned.encoding_surjective width)).step
      (fun pair => ((Addition.TTK.lowOutput pair.1.1, pair.1.2), pair.2)) state =
      (ArithmeticWindow.placement width length fits).step state := by
  exact (ArithmeticWindow.placement width length fits).subsystem.withFlag_step
    (ArithmeticTop.sign width) (ArithmeticTop.subsystem_sign_ne width length fits)
    (ArithmeticWindow.source_onto length) (ArithmeticTop.overflow_onto length)
    (Scanned.encoding_surjective width) Addition.TTK.lowOutput state

/-- The real low addition returns the full aligned original low remainder result. -/
lemma aligned_low {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (state : Data width) :
    (ArithmeticWindow.placement width window.length (fits window)).step
        ((ArithmeticAlignment.Fixed.frame width window.below).grouping state) =
      (ArithmeticAlignment.Fixed.frame width window.below).grouping
        (ArithmeticWindowProgram.step window .addLow state.1, state.2) :=
  (low_action width window.length (fits window) _).symm.trans
    (aligned_action window .addLow state)

/-- The real signed addition returns the full aligned original signed remainder result. -/
lemma aligned_signed {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (state : Data width) :
    ArithmeticTop.windowStep width window.length (fits window)
        ((ArithmeticAlignment.Fixed.frame width window.below).grouping state) =
      (ArithmeticAlignment.Fixed.frame width window.below).grouping
        (ArithmeticWindowProgram.step window .addSigned state.1, state.2) :=
  aligned_action window .addSigned state

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderCoordinates
