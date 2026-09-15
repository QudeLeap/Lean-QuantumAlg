/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Layout

/-!
# TTK six-stage gate lists

The six stages follow the source's increasing or decreasing bit-index orders.
Only actual CNOT and Toffoli gates are compiled. Carries occupy operand bits;
the low-word network omits gates whose sole target is the overflow output.
The overflow network restores those two top-bit gates and carries no extra
workspace [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open EncodedBit.GateSpec

/-- Stage one: xor every non-low addend bit into its target bit. -/
def preXorGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  List.ofFn fun i : Fin (n - 1) =>
    let j : Fin n := ⟨i.val + 1, by omega⟩
    .cnot (leftBit n j) (rightBit n j) (ttkLeftRight_disjoint n j j)

/-- Operand-only part of stage two, in descending bit order. -/
def descendingXorGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  (List.ofFn fun i : Fin (n - 2) =>
    let a : Fin n := ⟨i.val + 1, by omega⟩
    let b : Fin n := ⟨i.val + 2, by omega⟩
    .cnot (leftBit n a) (leftBit n b)
      (ttkLeftLeft_disjoint n a b (by
        intro h
        have hval := congrArg Fin.val h
        change i.val + 1 = i.val + 2 at hval
        omega))).reverse

/-- Operand-only part of stage three, propagating carries upwards. -/
def carryGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  List.ofFn fun i : Fin (n - 1) =>
    let a : Fin n := ⟨i.val, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    .toffoli (rightBit n a) (leftBit n a) (leftBit n b)
      (Ne.symm (ttkLeftRight_disjoint n a a))
      (Ne.symm (ttkLeftRight_disjoint n b a))
      (ttkLeftLeft_disjoint n a b (by
        intro h
        have hval := congrArg Fin.val h
        change i.val = i.val + 1 at hval
        omega))

/-- Stage four: extract each sum xor before undoing its operand-encoded carry.
Blocks are reversed as blocks, preserving CNOT-before-Toffoli inside each. -/
def descendingUncomputeGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  ((List.ofFn fun i : Fin (n - 1) =>
    let a : Fin n := ⟨i.val, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    [.cnot (leftBit n b) (rightBit n b) (ttkLeftRight_disjoint n b b),
     .toffoli (rightBit n a) (leftBit n a) (leftBit n b)
       (Ne.symm (ttkLeftRight_disjoint n a a))
       (Ne.symm (ttkLeftRight_disjoint n b a))
       (ttkLeftLeft_disjoint n a b (by
         intro h
         have hval := congrArg Fin.val h
         change i.val = i.val + 1 at hval
         omega))]
    ).reverse).flatten

/-- Stage five restores the operand-only xor chain in ascending order. -/
def ascendingXorGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  (descendingXorGates n).reverse

/-- Stage six xors the restored addend into every target bit. -/
def finalXorGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  List.ofFn fun i : Fin n =>
    .cnot (leftBit n i) (rightBit n i) (ttkLeftRight_disjoint n i i)

/-- TTK low-word gate list with no overflow wire or workspace. -/
def lowRippleGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  preXorGates n ++ descendingXorGates n ++ carryGates n ++
    descendingUncomputeGates n ++ ascendingXorGates n ++ finalXorGates n

/-- Compile the low-word list on exactly the two operand words. -/
def lowRippleProgram (n : Nat) : UnitaryCircuit (Qubits (encoding n).width) :=
  programList (lowRippleGates n)

/-- Direct compilation realizes the literal low-word gate fold. The separate
word-level proof must identify this fold with `lowOutput`. -/
theorem ttkLowRipple_realizes_fold (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (lowRippleProgram n)
      (stepList (lowRippleGates n)) := realizesList _

/-- The top CNOT in stage two targets the explicit overflow output. -/
def overflowPreGate (n : Nat) : EncodedBit.GateSpec (overflowEncoding (n + 1)) :=
  let top : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  .cnot (withOverflowBit (leftBit (n + 1) top)) (overflowBit (n + 1))
    (ttkWithOverflowBit_output_disjoint _)

/-- The top Toffoli in stage three completes the explicit output carry. -/
def overflowCarryGate (n : Nat) : EncodedBit.GateSpec (overflowEncoding (n + 1)) :=
  let top : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  .toffoli (withOverflowBit (rightBit (n + 1) top))
    (withOverflowBit (leftBit (n + 1) top)) (overflowBit (n + 1))
    (ttkWithOverflowBit_disjoint _ _
      (Ne.symm (ttkLeftRight_disjoint (n + 1) top top)))
    (ttkWithOverflowBit_output_disjoint _) (ttkWithOverflowBit_output_disjoint _)

/-- TTK overflow gate list. At width one stage two is empty, so its special
case has only the carry Toffoli and the final sum CNOT. -/
def overflowGates : (n : Nat) → List (EncodedBit.GateSpec (overflowEncoding n))
  | 0 => []
  | 1 => [overflowCarryGate 0] ++ (finalXorGates 1).map withOverflowGate
  | n + 2 =>
      (preXorGates (n + 2)).map withOverflowGate ++
      [overflowPreGate (n + 1)] ++
      (descendingXorGates (n + 2)).map withOverflowGate ++
      (carryGates (n + 2)).map withOverflowGate ++
      [overflowCarryGate (n + 1)] ++
      (descendingUncomputeGates (n + 2)).map withOverflowGate ++
      (ascendingXorGates (n + 2)).map withOverflowGate ++
      (finalXorGates (n + 2)).map withOverflowGate

/-- Compile the overflow list on exactly two operands and its output bit. -/
def overflowProgram (n : Nat) : UnitaryCircuit (Qubits (overflowEncoding n).width) :=
  programList (overflowGates n)

/-- Direct compilation realizes the literal overflow gate fold. -/
theorem ttkOverflow_realizes_fold (n : Nat) :
    UnitaryCircuit.Realizes (overflowEncoding n) (overflowProgram n)
      (stepList (overflowGates n)) := realizesList _

end

end QuantumAlg.MAU.Addition.TTK
