/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Remainder.Natural
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Preservation

/-! # Complete paid remainder-address preparation commutes with retained original arithmetic -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit

/-- The full actual finite address follows the same source transform, including its pool. -/
lemma remainderStep_liftSource (width : Nat) (positive : 1 ≤ width)
    (transform : Registers width → Registers width) (state : Data width)
    (retained : ∀ field, ArithmeticGeometry.fieldValue field (liftSource width transform state) =
      ArithmeticGeometry.fieldValue field state) :
    remainderStep width positive (liftSource width transform state) =
      liftSource width transform (remainderStep width positive state) := by
  apply Prod.ext
  · change (remainderStep width positive (liftSource width transform state)).1 =
      transform (remainderStep width positive state).1
    rw [remainderStep_source, remainderStep_source]
    rfl
  · apply Prod.ext
    · change (remainderStep width positive (liftSource width transform state)).2.1 =
        (remainderStep width positive state).2.1
      rw [remainderStep_address, remainderStep_address,
        sourceValue_liftSource width positive transform state .coefficient (retained .coefficient),
        sourceValue_liftSource width positive transform state .quotient (retained .quotient),
        sourceValue_liftSource width positive transform state .shift (retained .shift)]
      rfl
    · change (remainderStep width positive (liftSource width transform state)).2.2 =
        (remainderStep width positive state).2.2
      rw [remainderStep_workspace, remainderStep_workspace]
      rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderWindow

noncomputable section

open EncodedBit

/-- All four complete original metadata fields survive every original remainder arithmetic mode. -/
lemma original_field_retained (width : Nat)
    (selected : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (field : ArithmeticGeometry.Field)
    (state : Data width) :
    ArithmeticGeometry.fieldValue field
      (ArithmeticAddress.liftSource width (ArithmeticWindowProgram.step selected operation) state) =
        ArithmeticGeometry.fieldValue field state := by
  have retained := ArithmeticWindowPreservation.remainder_retained selected operation state.1
  cases field with
  | coefficient =>
      exact congrArg
        (fun value : ArithmeticWindowPreservation.Retained width => value.1.1) retained
  | quotient =>
      exact congrArg
        (fun value : ArithmeticWindowPreservation.Retained width => value.1.2) retained
  | divisor =>
      exact congrArg
        (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.1) retained
  | shift =>
      exact congrArg
        (fun value : ArithmeticWindowPreservation.Retained width => value.2.1.2) retained

/-- Full source arithmetic returns exactly the preparation of its complete original output. -/
lemma address_original_commute (width : Nat) (positive : 1 ≤ width)
    (selected : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (state : Data width) :
    ArithmeticAddress.remainderStep width positive
        (ArithmeticAddress.liftSource width (ArithmeticWindowProgram.step selected operation)
          state) =
      ArithmeticAddress.liftSource width (ArithmeticWindowProgram.step selected operation)
        (ArithmeticAddress.remainderStep width positive state) :=
  ArithmeticAddress.remainderStep_liftSource width positive
    (ArithmeticWindowProgram.step selected operation) state
    (fun field => original_field_retained width selected operation field state)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderWindow
