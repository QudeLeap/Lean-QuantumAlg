/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Stages
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Isometry
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Semantics
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Independent full-label injectivity of the actual measured multiplier on clean helpers

Each actual MAC has independently established clean-helper injectivity.
Only the intervening pure native word uses a native reversed gate list.
No reversed word or adjoint is assigned to either measured instrument
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open EncodedBit Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Equal complete actual outputs identify equal complete original clean-helper inputs. -/
lemma multiplicationWord_label_injective_clean (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (coefficient inverseCoefficient : Nat) (first second : Data)
    (firstClean : ∀ helper, (layout.clean helper).get first = false)
    (secondClean : ∀ helper, (layout.clean helper).get second = false)
    (same : wordLabel (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
      first = wordLabel (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
        second) : first = second := by
  rw [multiplicationWord_label_stages, multiplicationWord_label_stages] at same
  have firstSwappedClean : ∀ helper, (layout.clean helper).get
      (layout.exchangedLabel wide modulus coefficient first) = false := by
    intro helper
    exact (swapWordGates_clean layout _ helper).trans
      ((forwardLabel_frame layout wide modulus coefficient first firstClean).clean helper)
  have secondSwappedClean : ∀ helper, (layout.clean helper).get
      (layout.exchangedLabel wide modulus coefficient second) = false := by
    intro helper
    exact (swapWordGates_clean layout _ helper).trans
      ((forwardLabel_frame layout wide modulus coefficient second secondClean).clean helper)
  have exchangedSame := accumulatePrefixWord_label_injective_clean layout wide modulus
    (inverseConstant modulus inverseCoefficient) width le_rfl _ _
      firstSwappedClean secondSwappedClean same
  have forwardSame := congrArg (GateSpec.stepList layout.swapWordGates.reverse) exchangedSame
  change GateSpec.stepList layout.swapWordGates.reverse
      (GateSpec.stepList layout.swapWordGates
        (layout.forwardLabel wide modulus coefficient first)) =
    GateSpec.stepList layout.swapWordGates.reverse
      (GateSpec.stepList layout.swapWordGates (layout.forwardLabel wide modulus coefficient second))
    at forwardSame
  rw [GateSpec.stepList_reverse_stepList, GateSpec.stepList_reverse_stepList] at forwardSame
  exact accumulatePrefixWord_label_injective_clean layout wide modulus
    (forwardConstant modulus coefficient) width le_rfl
      first second firstClean secondClean forwardSame

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
