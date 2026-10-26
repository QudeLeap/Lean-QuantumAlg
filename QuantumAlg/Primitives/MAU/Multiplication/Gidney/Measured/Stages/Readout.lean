/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Stages
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Program
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Frame
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Accumulate.Arithmetic
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Swap.Semantics

/-!
# Independent word values at the actual forward/swap/explicit-inverse boundaries

The source after the native exchange is the actual forward modular product
on the selected branch. The target is the original source and therefore
supplies the canonical input needed by the explicit inverse MAC
[VBE95, 9511018.tex:333-367; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout

noncomputable section

open Addition.Gidney.Measured.Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual swapped source is exactly the independently computed selected modular product. -/
lemma exchangedLabel_source_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat) (coefficient : Nat)
    (initial : Data) (ready : layout.Ready modulus initial) :
    (layout.sourceWord (layout.exchangedLabel wide modulus coefficient initial)).toNat =
      if layout.control.get initial then
        ((layout.targetWord initial).toNat + coefficient * (layout.sourceWord initial).toNat) %
          modulus.toNat else (layout.sourceWord initial).toNat := by
  rw [exchangedLabel, swapWordGates_sourceWord,
    (forwardLabel_frame layout wide modulus coefficient initial ready.clean).control]
  cases enabled : layout.control.get initial
  · exact congrArg BitVec.toNat
      (forwardLabel_frame layout wide modulus coefficient initial ready.clean).source
  · have forward := forwardMACWord_target_nat layout wide modulus positive coefficient
      initial ready
    simpa only [forwardLabel, enabled, if_true] using forward

/-- The actual swapped target is exactly the original source on the selected branch. -/
lemma exchangedLabel_target_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat) (coefficient : Nat)
    (initial : Data) (ready : layout.Ready modulus initial) :
    (layout.targetWord (layout.exchangedLabel wide modulus coefficient initial)).toNat =
      if layout.control.get initial then (layout.sourceWord initial).toNat else
        (layout.targetWord initial).toNat := by
  rw [exchangedLabel, swapWordGates_targetWord,
    (forwardLabel_frame layout wide modulus coefficient initial ready.clean).control]
  cases enabled : layout.control.get initial
  · have forward := forwardMACWord_target_nat layout wide modulus positive coefficient
      initial ready
    simpa only [forwardLabel, enabled, Bool.false_eq_true, if_false] using forward
  · exact congrArg BitVec.toNat
      (forwardLabel_frame layout wide modulus coefficient initial ready.clean).source

/-- The complete actual word retains that same independently specified source product. -/
lemma multiplicationWord_source_nat (layout : Layout encoding width) (wide : 2 ≤ width)
    (modulus : BitVec width) (positive : 0 < modulus.toNat)
    (coefficient inverseCoefficient : Nat) (initial : Data) (ready : layout.Ready modulus initial) :
    (layout.sourceWord
      (wordLabel (layout.multiplicationWord wide modulus coefficient inverseCoefficient)
        initial)).toNat =
      if layout.control.get initial then
        ((layout.targetWord initial).toNat + coefficient * (layout.sourceWord initial).toNat) %
          modulus.toNat else (layout.sourceWord initial).toNat := by
  rw [multiplicationWord_label_stages,
    multipliedLabel_sourceWord layout wide modulus coefficient inverseCoefficient
      initial ready.clean]
  exact exchangedLabel_source_nat layout wide modulus positive coefficient initial ready

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Layout
