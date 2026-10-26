/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Top.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Encoding
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Program
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Source
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Compose
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Retain
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag.Action

/-!
# The same complete original coefficient action with the entire retained pool

The actual streamed body was proved separately. Here its complete
independent window action is identified with the original arithmetic
window at the identical source positions. Both arbitrary Sign and every
original saved bit are retained, together with the complete existing pool.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientCoordinates

noncomputable section

open EncodedBit

private lemma pool_onto (width : Nat) : Function.Surjective (poolEncoding width).encode :=
  Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective
    (Scanned.product_total _ _ BitVec.equivFin.toEquiv.surjective Scanned.bool_total)

/-- Identical source positions identify every full source action, retaining the original pool. -/
lemma frame_action (width length : Nat) (fits : length ≤ width + 3)
    (action : Addition.TTK.OverflowRegisters length → Addition.TTK.OverflowRegisters length)
    (state : Data width) :
    (templateFrame width length fits).step (fun pair => (action pair.1, pair.2)) state =
      ((CoefficientWindowProgram.placement (window width length fits)).step
        (fun pair => (action pair.1, pair.2)) state.1, state.2) := by
  have equality := (templateFrame width length fits).step_eq_of_source_wires
    (originalFrame width length fits) (ArithmeticTop.overflow_onto length)
    Function.surjective_id
    (Scanned.product_total _ _
      (ArithmeticWindowEncoding.complement_surjective (window width length fits)) (pool_onto width))
    (Scanned.encoding_surjective width) (source_positions width length fits) action state
  exact equality.trans (FullPlacement.retainRight_step
    (CoefficientWindowProgram.placement (window width length fits))
    (poolEncoding width) action state)

private lemma low_action (width length : Nat) (fits : length ≤ width + 3) (state : Data width) :
    ((ArithmeticTop.placement width length fits).full (ArithmeticTop.overflow_onto length)
        (Scanned.encoding_surjective width)).step
      (fun pair => ((Addition.TTK.lowOutput pair.1.1, pair.1.2), pair.2)) state =
      (ArithmeticWindow.placement width length fits).step state := by
  exact (ArithmeticWindow.placement width length fits).subsystem.withFlag_step
    (ArithmeticTop.sign width) (ArithmeticTop.subsystem_sign_ne width length fits)
    (ArithmeticWindow.source_onto length) (ArithmeticTop.overflow_onto length)
    (Scanned.encoding_surjective width) Addition.TTK.lowOutput state

/-- The full low or signed streamed coefficient action is exactly the original window action. -/
lemma windowStep_eq_original (width length : Nat) (fits : length ≤ width + 3)
    (signed : Bool) (state : Data width) :
    CoefficientWindow.windowStep width length fits signed state =
      (CoefficientWindowProgram.step (window width length fits)
        (if signed then ArithmeticWindowProgram.Operation.addSigned else .addLow) state.1,
          state.2) := by
  cases signed with
  | false =>
      have equality := frame_action width length fits
        (fun pair => (Addition.TTK.lowOutput pair.1, pair.2)) state
      rw [templateFrame, FullPlacement.compose_step] at equality
      have sameAction :
          (fun input : Data width =>
            ((ArithmeticTop.placement width length fits).full (ArithmeticTop.overflow_onto length)
              (Scanned.encoding_surjective width)).step
                (fun pair => ((Addition.TTK.lowOutput pair.1.1, pair.1.2), pair.2)) input) =
          (ArithmeticWindow.placement width length fits).step :=
        funext (low_action width length fits)
      change (CoefficientFrame.placement width).step
        (fun input : Data width =>
          ((ArithmeticTop.placement width length fits).full (ArithmeticTop.overflow_onto length)
            (Scanned.encoding_surjective width)).step
              (fun pair => ((Addition.TTK.lowOutput pair.1.1, pair.1.2), pair.2)) input) state = _
        at equality
      rw [sameAction] at equality
      exact equality
  | true =>
      have equality := frame_action width length fits Addition.TTK.overflowOutput state
      rw [templateFrame, FullPlacement.compose_step] at equality
      exact equality

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientCoordinates
