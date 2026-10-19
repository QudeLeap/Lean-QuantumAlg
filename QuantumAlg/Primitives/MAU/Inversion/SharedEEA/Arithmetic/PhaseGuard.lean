/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Guard
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control

/-!
# Native phase-and-sign predicates for the low arithmetic instructions

Remainder add-back reads `!Phase1 && (!Phase2 || !Sign)` after the signed
subtraction and phase-dependent Sign complement
[LYL+26, sec_EEA/sub_opt.tex:43-48]. Coefficient subtraction reads
`Phase1 && (Phase2 || !Sign)` before its Sign complement and signed
addition [LYL+26, sec_EEA/sub_opt.tex:61-66].

Each predicate is xored into the existing Ctrl using actual X, CNOT and
four-Toffoli dirty-control gates. The original Iter is arbitrary and is
restored, along with every phase and Sign bit. Reversing the emitted list
restores Ctrl after a body that preserves the predicate. Low arithmetic
has that property; these guards must not be kept across a signed update
of the Sign value they read.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticPhaseGuard

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit

private def flags (width : Nat) : Fin 5 → EncodedBit (encoding width) :=
  ![phase1Bit width, phase2Bit width, signBit width, iterationBit width, controlBit width]

private lemma flags_wire (width : Nat) (index : Fin 5) :
    (flags width index).wire.val = 2 * (width + 3) + 4 * width.size + index.val := by
  fin_cases index
  · exact phase1Bit_wire width
  · exact phase2Bit_wire width
  · exact signBit_wire width
  · exact iterationBit_wire width
  · exact controlBit_wire width

private lemma flags_ne (width : Nat) (left right : Fin 5) (different : left ≠ right) :
    (flags width left).wire ≠ (flags width right).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [flags_wire, flags_wire] at values
  apply different
  exact Fin.ext (by omega)

/-- The exact source predicate for coefficient subtraction or remainder add-back. -/
def predicate {width : Nat} (coefficient : Bool) (state : Registers width) : Bool :=
  if coefficient then state.flags.first && (state.flags.second || !state.flags.sign)
  else !state.flags.first && (!state.flags.second || !state.flags.sign)

private def tripleGate (width : Nat) : GateSpec (encoding width) :=
  .toffoli (flags width 1) (flags width 2) (flags width 4)
    (flags_ne width 1 2 (by decide)) (flags_ne width 1 4 (by decide))
    (flags_ne width 2 4 (by decide))

private lemma triple_control (width : Nat) :
    GateSpec.bitDisjoint (flags width 0) (tripleGate width) :=
  ⟨flags_ne width 1 0 (by decide), flags_ne width 2 0 (by decide),
    flags_ne width 4 0 (by decide)⟩

private lemma triple_work (width : Nat) :
    GateSpec.bitDisjoint (flags width 3) (tripleGate width) :=
  ⟨flags_ne width 1 3 (by decide), flags_ne width 2 3 (by decide),
    flags_ne width 4 3 (by decide)⟩

private def triple (width : Nat) : List (GateSpec (encoding width)) :=
  GateSpec.withDirtyControl (flags width 0) (flags width 3) (tripleGate width)
    (triple_control width) (triple_work width)
    (flags_ne width 0 3 (by decide))

private lemma triple_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (triple width) state =
      PhaseGuard.xorControl
        (state.flags.first && state.flags.second && state.flags.sign) state := by
  rw [triple, GateSpec.withDirtyControl_step]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨first, second, sign, iteration⟩, control⟩
  cases first <;> cases second <;> cases sign <;> cases control <;> rfl

private def before (width : Nat) (coefficient : Bool) : List (GateSpec (encoding width)) :=
  if coefficient then
    [.cnot (flags width 0) (flags width 4) (flags_ne width 0 4 (by decide)), .x (flags width 1)]
  else
    [.x (flags width 4),
      .cnot (flags width 0) (flags width 4) (flags_ne width 0 4 (by decide)), .x (flags width 0)]

private def after (width : Nat) (coefficient : Bool) : List (GateSpec (encoding width)) :=
  if coefficient then [.x (flags width 1)] else [.x (flags width 0)]

/-- Actual predicate computation and phase-mask restoration; Iter is restored within the triple. -/
def gates (width : Nat) (coefficient : Bool) : List (GateSpec (encoding width)) :=
  before width coefficient ++ triple width ++ after width coefficient

/-- Complete native execution xors precisely the source condition and retains all other fields. -/
lemma gates_step (width : Nat) (coefficient : Bool) (state : Registers width) :
    GateSpec.stepList (gates width coefficient) state =
      PhaseGuard.xorControl (predicate coefficient state) state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append, triple_step]
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨first, second, sign, iteration⟩, control⟩
  cases coefficient <;> cases first <;> cases second <;> cases sign <;> cases control <;> rfl

/-- Predicate computation leaves every bit read by that predicate unchanged. -/
lemma predicate_xorControl {width : Nat} (coefficient value : Bool) (state : Registers width) :
    predicate coefficient (PhaseGuard.xorControl value state) = predicate coefficient state := rfl

private lemma xorControl_twice {width : Nat} (value : Bool) (state : Registers width) :
    PhaseGuard.xorControl value (PhaseGuard.xorControl value state) = state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, phases, control⟩
  cases value <;> cases control <;> rfl

/-- The actual inverse gate list has the same predicate xor action on every complete input. -/
lemma reverse_step (width : Nat) (coefficient : Bool) (state : Registers width) :
    GateSpec.stepList (gates width coefficient).reverse state =
      PhaseGuard.xorControl (predicate coefficient state) state := by
  have inverse := GateSpec.stepList_reverse_stepList (gates width coefficient)
    (PhaseGuard.xorControl (predicate coefficient state) state)
  rw [gates_step, predicate_xorControl, xorControl_twice] at inverse
  exact inverse

/-- Actual quantum amplitudes of the computed predicate, for arbitrary Ctrl and Iter. -/
lemma program_realizes (width : Nat) (coefficient : Bool) :
    UnitaryCircuit.Realizes (encoding width)
      (GateSpec.programList (QubitLayout.canonical _) .empty (gates width coefficient)) environment
      (fun state => PhaseGuard.xorControl (predicate coefficient state) state) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width coefficient) (gates_step width coefficient) environment

/-- Exact predicate size includes every actual negative-control mask and its inverse. -/
lemma gates_length (width : Nat) (coefficient : Bool) :
    (gates width coefficient).length = if coefficient then 7 else 8 := by
  rw [gates, List.length_append, List.length_append, triple,
    GateSpec.withDirtyControl_length]
  cases coefficient <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticPhaseGuard
