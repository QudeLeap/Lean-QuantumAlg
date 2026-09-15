/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Program
import all QuantumAlg.Components.Encoded.BitGates.Control

/-!
# A coherent variable-product stage on three existing words

One bit of the first quantum input controls the existing multiply-accumulate
with compile-time coefficient `2^i`. Its inner source-bit stages therefore
add `2^(i+j)` selected by the two original quantum input bits. Neither input
is converted to a classical coefficient. The complete carrier consists of
the two inputs and the target, with no additional quantum workspace.

This is the binary controlled-add construction [VBE95, 9511018.tex:333-367]
using the exact modular offsets [G17, paper.tex:319-334]. All widths, zero
inputs, even moduli and noncanonical target labels retain the underlying
total unitary extension. No inverse input is required.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

open Nat.FixedWidth

/-- Two unchanged quantum input words followed by the modular accumulator. -/
abbrev Registers (width : Nat) := Fin (2 ^ width) × Accumulate.Gidney.Registers width

/-- The complete three-word binary carrier. -/
def encoding (width : Nat) : BinaryLabelEncoding (Registers width) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
    (Accumulate.Gidney.encoding width)

/-- Read an original input bit in the fixed little-endian convention. -/
def inputBit (width : Nat) (index : Fin width) :
    EncodedBit (BinaryLabelEncoding.finIdentity width) :=
  BinaryLabelEncoding.finIdentityBit width (WireAddress.littleEndianWire index)

theorem variableGidney_inputBit_get (width : Nat) (index : Fin width)
    (input : Fin (2 ^ width)) :
    (inputBit width index).get input = input.val.testBit index.val := by
  change input.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

/-- Independent total finite-word action of one selected input-bit stage. -/
def stageOutput {width : Nat} (modulus : Fin (2 ^ width + 1)) (index : Fin width)
    (state : Registers width) : Registers width :=
  (state.1, if state.1.val.testBit index.val then
    Accumulate.Gidney.prefixOutput modulus (2 ^ index.val) width state.2 else state.2)

/-- Actual coherent control of the existing native two-word MAC. -/
def stageProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) (index : Fin width) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.controlAtEncodedBit (inputBit width index)
    (Accumulate.Gidney.program width modulus (2 ^ index.val))

/-- Exact action of both coherent branches on every complete encoded label. -/
theorem variableGidney_stage_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    UnitaryCircuit.Realizes (encoding width) (stageProgram width modulus index)
      (stageOutput modulus index) where
  apply_encoded_ket := by
    rintro ⟨input, state⟩
    have actual := UnitaryCircuit.controlAtEncodedBit_applyNormalized_of_eq
      (inputBit width index) (Accumulate.Gidney.encoding width)
      (Accumulate.Gidney.program width modulus (2 ^ index.val)) state
      (Accumulate.Gidney.prefixOutput modulus (2 ^ index.val) width state)
      ((Accumulate.Gidney.gidneyAccumulate_realizes width modulus
        (2 ^ index.val)).apply_encoded_ket state) input
    rw [variableGidney_inputBit_get] at actual
    exact actual

/-- Every quantum input coordinate is preserved, including the selected control. -/
theorem variableGidney_stage_inputs (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) (state : Registers width) :
    (stageOutput modulus index state).1 = state.1 ∧
      (stageOutput modulus index state).2.1 = state.2.1 := by
  constructor
  · rfl
  · unfold stageOutput
    split_ifs <;> rfl

/-- All accessed physical positions lie in the original three words. -/
theorem variableGidney_stage_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).physical_idx ⊆ List.range (encoding width).width := by
  apply UnitaryCircuit.controlAtEncodedBit_physical_idx_subset_range
  rw [Accumulate.Gidney.gidneyAccumulate_physical]
  change List.range (2 * width) ⊆ List.range (width + width)
  simp only [Nat.two_mul]
  exact List.Subset.refl _

end

end QuantumAlg.MAU.Multiplication.VariableGidney
