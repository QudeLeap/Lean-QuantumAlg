/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Actual source-phase predicates in the existing Ctrl wire

The optimized source separates the pre-shift Phase1-zero block from the
post-shift Phase1-one block, with Phase2 selecting descending shifts
[LYL+26, sec_EEA/sub_opt.tex:37-40,52-70]. The native lists below xor each
corresponding predicate into the existing Ctrl, and retain every other
field. Their literal inverses restore the old Ctrl for arbitrary input
values. No incoming-zero assumption is made by these full-frame laws.

The complete initialized algorithm establishes Ctrl-zero internally. A
later compute/use/inverse-cleanup composition may use that invariant to
select its actual body; the guard itself neither allocates storage nor
turns a retained phase value into a classical circuit parameter.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PhaseGuard

noncomputable section

open EncodedBit

private theorem first_control (width : Nat) :
    (phase1Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase1Bit_wire, controlBit_wire] at values
  omega

private theorem second_control (width : Nat) :
    (phase2Bit width).wire ≠ (controlBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase2Bit_wire, controlBit_wire] at values
  omega

private theorem first_second (width : Nat) :
    (phase1Bit width).wire ≠ (phase2Bit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [phase1Bit_wire, phase2Bit_wire] at values
  omega

/-- Retain the old Ctrl and xor a computed predicate into that same physical bit. -/
def xorControl {width : Nat} (value : Bool) (state : Registers width) : Registers width :=
  { state with control := state.control ^^ value }

/-- The actual phase field selects the pre-shift or post-shift source block. -/
def firstPredicate {width : Nat} (selected : Bool) (state : Registers width) : Bool :=
  decide (state.flags.first = selected)

/-- Descending shifts additionally read the retained Phase2 field. -/
def descendingPredicate {width : Nat} (selected : Bool) (state : Registers width) : Bool :=
  firstPredicate selected state && state.flags.second

/-- A positive phase condition is one CNOT; its negative condition also xors the constant one. -/
def firstGates (width : Nat) (selected : Bool) : List (GateSpec (encoding width)) :=
  if selected then [.cnot (phase1Bit width) (controlBit width) (first_control width)]
  else [.x (controlBit width), .cnot (phase1Bit width) (controlBit width) (first_control width)]

/-- One actual Toffoli, conjugated by Phase1 X gates for the negative source condition. -/
def descendingGates (width : Nat) (selected : Bool) : List (GateSpec (encoding width)) :=
  let gate := GateSpec.toffoli (phase1Bit width) (phase2Bit width) (controlBit width)
    (first_second width) (first_control width) (second_control width)
  if selected then [gate] else [.x (phase1Bit width), gate, .x (phase1Bit width)]

/-- Full-register action of the literal phase-condition gate list, with arbitrary incoming Ctrl. -/
theorem first_step (width : Nat) (selected : Bool) (state : Registers width) :
    GateSpec.stepList (firstGates width selected) state =
      xorControl (firstPredicate selected state) state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases selected <;> cases p1 <;> cases control <;> rfl

/-- The literal descending-condition list restores both phase fields and all remaining systems. -/
theorem descending_step (width : Nat) (selected : Bool) (state : Registers width) :
    GateSpec.stepList (descendingGates width selected) state =
      xorControl (descendingPredicate selected state) state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases selected <;> cases p1 <;> cases p2 <;> cases control <;> rfl

/-- The actual inverse phase-condition list has the same predicate-xor action. -/
theorem first_reverse_step (width : Nat) (selected : Bool) (state : Registers width) :
    GateSpec.stepList (firstGates width selected).reverse state =
      xorControl (firstPredicate selected state) state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iter⟩, control⟩
  cases selected <;> cases p1 <;> cases control <;> rfl

/-- The literal reverse retains the same reversible predicate xor and preserves phase history. -/
theorem descending_reverse_step (width : Nat) (selected : Bool) (state : Registers width) :
    GateSpec.stepList (descendingGates width selected).reverse state =
      xorControl (descendingPredicate selected state) state := by
  have palindrome : (descendingGates width selected).reverse = descendingGates width selected := by
    cases selected <;> rfl
  rw [palindrome]
  exact descending_step width selected state

/-- Exact native realization of the retained phase predicate. -/
theorem first_realizes (width : Nat) (selected : Bool) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (firstGates width selected))
      (fun state => xorControl (firstPredicate selected state) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (firstGates width selected) (first_step width selected)

/-- Exact native realization of the retained descending-phase predicate. -/
theorem descending_realizes (width : Nat) (selected : Bool) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (descendingGates width selected))
      (fun state => xorControl (descendingPredicate selected state) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (descendingGates width selected) (descending_step width selected)

/-- Literal phase predicate size, including the constant-X gate for the negative condition. -/
theorem first_length (width : Nat) (selected : Bool) :
    (firstGates width selected).length = if selected then 1 else 2 := by
  cases selected <;> rfl

/-- Literal descending predicate size, including both actual Phase1 restoration X gates. -/
theorem descending_length (width : Nat) (selected : Bool) :
    (descendingGates width selected).length = if selected then 1 else 3 := by
  cases selected <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.PhaseGuard
