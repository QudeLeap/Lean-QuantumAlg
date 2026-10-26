/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Window.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Window.Program

/-!
# Original coefficient arithmetic commutes with complete actual address preparation

All four original finite length words and the complete Phase2 bit survive
every original coefficient arithmetic mode. The actual coherent address
therefore has the same full prepared output on both sides of the operation,
including arbitrary original pool values. Actual middle-program realization
and its admitted range remain separate obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow

noncomputable section

open EncodedBit

/-- Every complete finite source-length operand survives original coefficient arithmetic. -/
lemma original_field_retained (width : Nat)
    (selected : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (field : ArithmeticGeometry.Field)
    (state : Data width) :
    ArithmeticGeometry.fieldValue field
      (ArithmeticAddress.liftSource width
        (CoefficientWindowProgram.step selected operation) state) =
        ArithmeticGeometry.fieldValue field state := by
  have retained := ArithmeticWindowPreservation.coefficient_retained selected operation state.1
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

/-- Complete actual native address action commutes with the original full coefficient action. -/
lemma runtimeAddress_original_commute (width : Nat) (positive : 1 ≤ width)
    (selected : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (state : Data width) :
    ArithmeticAddress.runtimeCoefficientStep width positive
        (ArithmeticAddress.liftSource width (CoefficientWindowProgram.step selected operation)
          state) =
      ArithmeticAddress.liftSource width (CoefficientWindowProgram.step selected operation)
        (ArithmeticAddress.runtimeCoefficientStep width positive state) := by
  have retained := ArithmeticWindowPreservation.coefficient_retained selected operation state.1
  exact ArithmeticAddress.runtimeCoefficientStep_liftSource width positive
    (CoefficientWindowProgram.step selected operation) state
    (fun field => original_field_retained width selected operation field state)
    (congrArg (fun value : ArithmeticWindowPreservation.Retained width => value.2.2.1.2) retained)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientWindow
