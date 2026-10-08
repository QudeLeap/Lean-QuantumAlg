/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Gates
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Product
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Small

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

open Nat.FixedWidth EncodedBit GateSpec

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

private theorem inputBits_wire (width : Nat)
    (position : Fin (BinaryLabelEncoding.finIdentity width).width) :
    (BinaryLabelEncoding.finIdentityBit width position).wire = position := rfl

/-- Every bit of the inner two-word MAC has its original physical position. -/
private def bodyBits (width : Nat) :
    Fin (Accumulate.Gidney.encoding width).width →
      EncodedBit (Accumulate.Gidney.encoding width) :=
  productBit (BinaryLabelEncoding.finIdentityBit width)
    (BinaryLabelEncoding.finIdentityBit width)

private theorem bodyBits_wire (width : Nat)
    (position : Fin (Accumulate.Gidney.encoding width).width) :
    (bodyBits width position).wire = position :=
  productBit_wire (left := BinaryLabelEncoding.finIdentity width)
    (right := BinaryLabelEncoding.finIdentity width)
    (BinaryLabelEncoding.finIdentityBit width)
    (BinaryLabelEncoding.finIdentityBit width) (fun _ => rfl) (fun _ => rfl) position

/-- Actual controlled X/CNOT/Toffoli list on precisely the original three words. -/
def stageGates (width : Nat) (modulus : Fin (2 ^ width + 1)) (index : Fin width) :
    List (GateSpec
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
        (Accumulate.Gidney.encoding width))) :=
  if small : width ≤ 1 then
    (Accumulate.Gidney.gates width modulus (2 ^ index.val)).map
      (controlSmall (inputBit width index)
        (by change width + width ≤ 2; omega))
  else
    controlRightList (BinaryLabelEncoding.finIdentityBit width) (bodyBits width)
      (inputBits_wire width) (bodyBits_wire width)
      (by
        change 5 ≤ width + (width + width)
        omega)
      (inputBit width index)
      (Accumulate.Gidney.gates width modulus (2 ^ index.val))

/-- Both control branches preserve the whole first input and exact inner MAC action. -/
theorem variableGidney_stageGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) (state : Registers width) :
    stepList (stageGates width modulus index) state = stageOutput modulus index state := by
  by_cases small : width ≤ 1
  · simp only [stageGates, dif_pos small]
    rw [controlSmallList_step, Accumulate.Gidney.gidneyAccumulateGates_step,
      variableGidney_inputBit_get]
    rfl
  · simp only [stageGates, dif_neg small]
    rw [controlRightList_step, Accumulate.Gidney.gidneyAccumulateGates_step,
      variableGidney_inputBit_get]
    rfl

/-- Native circuit of the literal controlled list in the selected gate model. -/
def stageProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) (index : Fin width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (stageGates width modulus index)

/-- Exact action of both coherent branches on every complete encoded label. -/
theorem variableGidney_stage_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    UnitaryCircuit.Realizes (encoding width) (stageProgram width modulus index)
      (stageOutput modulus index) :=
  realizesList_congrStep _ _ _ (variableGidney_stageGates_step width modulus index)

/-- Every quantum input coordinate is preserved, including the selected control. -/
theorem variableGidney_stage_inputs (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) (state : Registers width) :
    (stageOutput modulus index state).1 = state.1 ∧
      (stageOutput modulus index state).2.1 = state.2.1 := by
  constructor
  · rfl
  · unfold stageOutput
    split_ifs <;> rfl

/-- The typed physical layout is exactly the three original words. -/
theorem variableGidney_stage_interface (width : Nat) :
    (encoding width).width = 3 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (3 * width) := by
  have size : (encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  exact ⟨size, (QubitLayout.canonical_systemIdx _).trans (congrArg List.range size)⟩

end

end QuantumAlg.MAU.Multiplication.VariableGidney
