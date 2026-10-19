/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.LocalAction
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# Boundary-width TTK adders

Zero-, one-, and two-bit addition are specified independently of the source's
`n >= 3` resource calculation. Low-word addition uses exactly the operand
qubits; overflow addition has one explicit output qubit whose initial value
is arbitrary. The one- and two-bit overflow gate lists are the TTK six-stage
construction specialized to their widths. The two-bit low-word circuit
directly writes its sole carry into the high target bit [TTK09,
qic-loglogaddition-quant.tex:285-318,357-372].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open BinaryLabelEncoding
open EncodedBit.GateSpec

namespace Zero

/-- No operation and no qubit are needed for two zero-width operands. -/
def lowProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical 0).toQuantum :=
  programList (encoding := finIdentity 0) (QubitLayout.canonical 0) .empty []

/-- Zero-width operands produce no overflow, preserving its arbitrary bit. -/
def overflowProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical 1).toQuantum :=
  programList (encoding := bool) (QubitLayout.canonical 1) .empty []

lemma ttkZeroLow_realizes : UnitaryCircuit.Realizes (finIdentity 0) lowProgram environment id :=
  realizesList (encoding := finIdentity 0) (QubitLayout.canonical 0) .empty [] environment

lemma ttkZeroOverflow_realizes : UnitaryCircuit.Realizes bool overflowProgram environment id :=
  realizesList (encoding := bool) (QubitLayout.canonical 1) .empty [] environment

end Zero

namespace One

/-- Two one-bit operand registers, with no workspace. -/
def lowEncoding : BinaryLabelEncoding (Bool × Bool) := prod bool bool

private def leftBit : EncodedBit lowEncoding := prodLeftBit bool bool boolBit
private def rightBit : EncodedBit lowEncoding := prodRightBit bool bool boolBit

/-- The one-bit low-word adder is one CNOT. -/
def lowGates : List (EncodedBit.GateSpec lowEncoding) :=
  [.cnot leftBit rightBit (by decide)]

/-- The actual two-qubit one-bit adder. -/
def lowProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical 2).toQuantum :=
  programList (QubitLayout.canonical 2) .empty lowGates

lemma ttkOneLow_step (a b : Bool) :
    stepList lowGates (a, b) = (a, b ^^ a) := by
  cases a <;> cases b <;> rfl

lemma ttkOneLow_realizes :
    UnitaryCircuit.Realizes lowEncoding lowProgram environment (fun s => (s.1, s.2 ^^ s.1)) :=
  realizesList_congrStep (encoding := lowEncoding) (QubitLayout.canonical 2) .empty lowGates
    (fun s => ttkOneLow_step s.1 s.2) environment

/-- The low output and carry satisfy ordinary one-bit integer addition. -/
lemma ttkOne_arithmetic (a b : Bool) :
    (b ^^ a).toNat + 2 * (a && b).toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> rfl

/-- The third qubit is an explicit overflow output, not a scratch bit. -/
def overflowEncoding : BinaryLabelEncoding ((Bool × Bool) × Bool) :=
  prod lowEncoding bool

private def overflowLeft : EncodedBit overflowEncoding :=
  prodLeftBit lowEncoding bool leftBit
private def overflowRight : EncodedBit overflowEncoding :=
  prodLeftBit lowEncoding bool rightBit
private def overflowBit : EncodedBit overflowEncoding :=
  prodRightBit lowEncoding bool boolBit

/-- The one-bit overflow adder computes carry before changing its target. -/
def overflowGates : List (EncodedBit.GateSpec overflowEncoding) :=
  [.toffoli overflowLeft overflowRight overflowBit (by decide) (by decide) (by decide),
   .cnot overflowLeft overflowRight (by decide)]

/-- The actual three-qubit one-bit overflow adder. -/
def overflowProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical 3).toQuantum :=
  programList (QubitLayout.canonical 3) .empty overflowGates

lemma ttkOneOverflow_step (a b z : Bool) :
    stepList overflowGates ((a, b), z) = ((a, b ^^ a), z ^^ (a && b)) := by
  cases a <;> cases b <;> cases z <;> rfl

lemma ttkOneOverflow_realizes :
    UnitaryCircuit.Realizes overflowEncoding overflowProgram environment
      (fun s => ((s.1.1, s.1.2 ^^ s.1.1), s.2 ^^ (s.1.1 && s.1.2))) :=
  realizesList_congrStep (encoding := overflowEncoding)
    (QubitLayout.canonical 3) .empty overflowGates
    (fun s => ttkOneOverflow_step s.1.1 s.1.2 s.2) environment

end One

namespace Two

/-- Four operand bits, with each word written in little-endian semantic order. -/
def lowEncoding : BinaryLabelEncoding ((Bool × Bool) × (Bool × Bool)) :=
  prod One.lowEncoding One.lowEncoding

private def wordLow : EncodedBit One.lowEncoding := prodLeftBit bool bool boolBit
private def wordHigh : EncodedBit One.lowEncoding := prodRightBit bool bool boolBit
private def a0 : EncodedBit lowEncoding :=
  prodLeftBit One.lowEncoding One.lowEncoding wordLow
private def a1 : EncodedBit lowEncoding :=
  prodLeftBit One.lowEncoding One.lowEncoding wordHigh
private def b0 : EncodedBit lowEncoding :=
  prodRightBit One.lowEncoding One.lowEncoding wordLow
private def b1 : EncodedBit lowEncoding :=
  prodRightBit One.lowEncoding One.lowEncoding wordHigh

/-- The two-bit low-word circuit writes its sole carry directly to the high
target bit, followed by the two operand-to-target CNOTs. -/
def lowGates : List (EncodedBit.GateSpec lowEncoding) :=
  [.toffoli a0 b0 b1 (by decide) (by decide) (by decide),
   .cnot a1 b1 (by decide), .cnot a0 b0 (by decide)]

/-- The actual four-qubit two-bit low-word adder. -/
def lowProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical 4).toQuantum :=
  programList (QubitLayout.canonical 4) .empty lowGates

/-- The independently stated two-bit arithmetic output. -/
def sumBits (a b : Bool × Bool) : Bool × Bool :=
  (b.1 ^^ a.1, (b.2 ^^ (a.1 && b.1)) ^^ a.2)

lemma ttkTwoLow_step (a b : Bool × Bool) :
    stepList lowGates (a, b) = (a, sumBits a b) := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

lemma ttkTwoLow_realizes :
    UnitaryCircuit.Realizes lowEncoding lowProgram environment (fun s => (s.1, sumBits s.1 s.2)) :=
  realizesList_congrStep (encoding := lowEncoding) (QubitLayout.canonical 4) .empty lowGates
    (fun s => ttkTwoLow_step s.1 s.2) environment

/-- The two-bit output agrees with integer addition modulo four. -/
lemma ttkTwoLow_arithmetic (a b : Bool × Bool) :
    (sumBits a b).1.toNat + 2 * (sumBits a b).2.toNat =
      (a.1.toNat + 2 * a.2.toNat + (b.1.toNat + 2 * b.2.toNat)) % 4 := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

/-- Four operand bits and a fifth explicit overflow output. -/
def overflowEncoding : BinaryLabelEncoding
    (((Bool × Bool) × (Bool × Bool)) × Bool) := prod lowEncoding bool

private def lift (bit : EncodedBit lowEncoding) : EncodedBit overflowEncoding :=
  prodLeftBit lowEncoding bool bit
private def z : EncodedBit overflowEncoding := prodRightBit lowEncoding bool boolBit

/-- The eight-gate specialization of the TTK overflow construction at width two. -/
def overflowGates : List (EncodedBit.GateSpec overflowEncoding) :=
  [.cnot (lift a1) (lift b1) (by decide),
   .cnot (lift a1) z (by decide),
   .toffoli (lift b0) (lift a0) (lift a1) (by decide) (by decide) (by decide),
   .toffoli (lift b1) (lift a1) z (by decide) (by decide) (by decide),
   .cnot (lift a1) (lift b1) (by decide),
   .toffoli (lift b0) (lift a0) (lift a1) (by decide) (by decide) (by decide),
   .cnot (lift a0) (lift b0) (by decide),
   .cnot (lift a1) (lift b1) (by decide)]

/-- The actual five-qubit two-bit overflow adder. -/
def overflowProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical 5).toQuantum :=
  programList (QubitLayout.canonical 5) .empty overflowGates

lemma ttkTwoOverflow_step (a b : Bool × Bool) (out : Bool) :
    stepList overflowGates ((a, b), out) =
      ((a, sumBits a b), out ^^ Bool.carry a.2 b.2 (a.1 && b.1)) := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases out <;> rfl

lemma ttkTwoOverflow_realizes :
    UnitaryCircuit.Realizes overflowEncoding overflowProgram environment
      (fun s => ((s.1.1, sumBits s.1.1 s.1.2),
        s.2 ^^ Bool.carry s.1.1.2 s.1.2.2 (s.1.1.1 && s.1.2.1))) :=
  realizesList_congrStep (encoding := overflowEncoding)
    (QubitLayout.canonical 5) .empty overflowGates
    (fun s => ttkTwoOverflow_step s.1.1 s.1.2 s.2) environment

/-- The overflow bit completes exact integer addition of two two-bit words. -/
lemma ttkTwoOverflow_arithmetic (a b : Bool × Bool) :
    (sumBits a b).1.toNat + 2 * (sumBits a b).2.toNat +
        4 * (Bool.carry a.2 b.2 (a.1 && b.1)).toNat =
      a.1.toNat + 2 * a.2.toNat + (b.1.toNat + 2 * b.2.toNat) := by
  rcases a with ⟨a0, a1⟩
  rcases b with ⟨b0, b1⟩
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> rfl

end Two

end

end QuantumAlg.MAU.Addition.TTK
