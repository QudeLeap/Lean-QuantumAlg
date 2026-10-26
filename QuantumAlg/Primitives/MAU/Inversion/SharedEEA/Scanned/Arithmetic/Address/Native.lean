/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Native.Support

/-!
# Literal native address arithmetic with separate conjunction

The original address-only operands are unchanged public subwords of
the full geometry frame. Every native instruction is emitted on those
actual positions; both arithmetic orientations retain their full
finite-word semantics and complete physical complement.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit

/-- The original address adder or its literal native reverse, without a geometry carry target. -/
def nativeFieldGates (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (subtract : Bool) : List (GateSpec (encoding width)) :=
  if subtract then (placement width positive field).nativeGates.reverse
  else (placement width positive field).nativeGates

/-- Both actual native orientations retain every original source and separate workspace bit. -/
lemma nativeFieldGates_step (width : Nat) (positive : 1 ≤ width) (field : ArithmeticGeometry.Field)
    (subtract : Bool) (state : Data width) :
    GateSpec.stepList (nativeFieldGates width positive field subtract) state =
      if subtract then subtractStep width positive field state
      else step width positive field state := by
  cases subtract with
  | false => exact (placement width positive field).nativeGates_step state
  | true =>
      have inverse := GateSpec.stepList_reverse_stepList
        (placement width positive field).nativeGates (subtractStep width positive field state)
      rw [Addition.TTK.WordPlacement.nativeGates_step] at inverse
      change GateSpec.stepList (placement width positive field).nativeGates.reverse
        (step width positive field (subtractStep width positive field state)) = _ at inverse
      rw [step_subtractStep] at inverse
      exact inverse

/-- Every actual address primitive excludes original word and source flag positions. -/
lemma nativeFieldGates_bitDisjoint (width : Nat) (positive : 1 ≤ width)
    (field : ArithmeticGeometry.Field) (subtract : Bool)
    (observed : EncodedBit (SharedEEA.encoding width))
    (outside : ArithmeticGeometry.outsideMetadata width observed) (gate : GateSpec (encoding width))
    (present : gate ∈ nativeFieldGates width positive field subtract) :
    GateSpec.bitDisjoint (sourceBit width observed) gate := by
  have original : gate ∈ (placement width positive field).nativeGates := by
    cases subtract <;>
      simpa only [nativeFieldGates, Bool.false_eq_true, if_false, if_true, List.mem_reverse]
        using present
  exact (placement width positive field).nativeGates_bitDisjoint (sourceBit width observed)
    (fun index => ArithmeticGeometry.source_outside width positive field observed outside
      index.succ)
    (fun index => ArithmeticGeometry.target_outside width observed index.succ) gate original

/-- Actual X instructions load the public address constant on the original ordered address only. -/
def nativeConstantGates (width : Nat)
    (constant : BitVec (NumberTheory.SharedEEA.ScanMetadata.addressWidth width)) :
    List (GateSpec (encoding width)) :=
  (littleTarget width).xorConstantGates constant.toFin

/-- Native constant loading has precisely its original complete physical address action. -/
lemma nativeConstantGates_step (width : Nat)
    (constant : BitVec (NumberTheory.SharedEEA.ScanMetadata.addressWidth width))
    (state : Data width) :
    GateSpec.stepList (nativeConstantGates width constant) state =
      constantStep width constant state := rfl

/-- Every actual constant-load operand excludes the original source register frame. -/
lemma nativeConstantGates_bitDisjoint (width : Nat)
    (constant : BitVec (NumberTheory.SharedEEA.ScanMetadata.addressWidth width))
    (observed : EncodedBit (SharedEEA.encoding width)) (gate : GateSpec (encoding width))
    (present : gate ∈ nativeConstantGates width constant) :
    GateSpec.bitDisjoint (sourceBit width observed) gate := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
  exact (source_address_ne width observed index.rev).symm

/-- Both fixed source-phase address bodies expose all actual native arithmetic instructions. -/
def nativeCoefficientGates (width : Nat) (positive : 1 ≤ width) (deshift : Bool) :
    List (GateSpec (encoding width)) :=
  if deshift then nativeConstantGates width (coefficientConstant width) ++
    (nativeFieldGates width positive .divisor true ++ nativeFieldGates width positive .shift true)
  else nativeFieldGates width positive .coefficient false

/-- The actual native word has the independent complete coefficient address action. -/
lemma nativeCoefficientGates_step (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (state : Data width) :
    GateSpec.stepList (nativeCoefficientGates width positive deshift) state =
      coefficientStep width positive deshift state := by
  cases deshift <;>
    simp only [nativeCoefficientGates, Bool.false_eq_true, if_false, if_true,
      GateSpec.stepList_append, nativeConstantGates_step, nativeFieldGates_step, coefficientStep]

/-- Every actual fixed address word excludes the original quantum operands and source flags. -/
lemma nativeCoefficientGates_bitDisjoint (width : Nat) (positive : 1 ≤ width) (deshift : Bool)
    (observed : EncodedBit (SharedEEA.encoding width))
    (outside : ArithmeticGeometry.outsideMetadata width observed) (gate : GateSpec (encoding width))
    (present : gate ∈ nativeCoefficientGates width positive deshift) :
    GateSpec.bitDisjoint (sourceBit width observed) gate := by
  cases deshift with
  | false =>
      exact nativeFieldGates_bitDisjoint width positive .coefficient false
        observed outside gate present
  | true =>
      have members : gate ∈ nativeConstantGates width (coefficientConstant width) ∨
          gate ∈ nativeFieldGates width positive .divisor true ∨
          gate ∈ nativeFieldGates width positive .shift true := by
        simpa only [nativeCoefficientGates, if_true, List.mem_append] using present
      rcases members with constant | divisor | shift
      · exact nativeConstantGates_bitDisjoint width _ observed gate constant
      · exact nativeFieldGates_bitDisjoint width positive .divisor true
          observed outside gate divisor
      · exact nativeFieldGates_bitDisjoint width positive .shift true observed outside gate shift

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
