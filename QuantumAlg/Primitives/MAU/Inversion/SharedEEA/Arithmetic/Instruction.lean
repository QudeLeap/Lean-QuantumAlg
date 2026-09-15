/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Selector

/-!
# The four actual source arithmetic instructions and their finite windows

The remainder window starts after the coefficient, separator, and quotient
and excludes the rotated suffix. Phase three uses its fixed little-endian
coefficient prefix; phase four reads the entire remaining coefficient region
through the actual divisor boundary [LYL+26, sec_EEA/sub_regshare.tex:278,291-298].
This includes high integer bits that the source's same-range comment can omit. All
positions below use untruncated Nat values of the actual finite fields.
A fixed key outside those physical bounds or with zero divisor length
contributes an identity program. The latter test prevents a terminal
rotation from exposing unrelated data through the original short window.

The four phase conditions are those of the actual optimized source blocks
[LYL+26, sec_EEA/sub_opt.tex:43-48,61-66]. Their fixed keys determine static
native circuits. The quantum input is tested only by the actual equality
program, and each selected arithmetic body uses the existing original Ctrl
and restores arbitrary Iter. Sign complement and inter-phase exchange are
separate actual source operations and are not hidden in these instructions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticInstruction

noncomputable section

open ArithmeticWindowRegisters ArithmeticWindowProgram ArithmeticWindowPreservation
open ArithmeticSelectionKey

/-- The four arithmetic operations in their source positions, before separate Sign updates. -/
inductive Instruction where
  | remainderSubtract
  | remainderAddback
  | coefficientSubtract
  | coefficientAdd
deriving DecidableEq

/-- The precise existing TTK arithmetic mode used by this source instruction. -/
def operation : Instruction → Operation
  | .remainderSubtract => .subtractSigned
  | .remainderAddback => .addLow
  | .coefficientSubtract => .subtractLow
  | .coefficientAdd => .addSigned

/-- Whether the actual arithmetic is placed in the original little-endian coefficient prefix. -/
def coefficient : Instruction → Bool
  | .remainderSubtract | .remainderAddback => false
  | .coefficientSubtract | .coefficientAdd => true

/-- The actual source key omits Sign precisely when its body can update Sign. -/
def includeSign (instruction : Instruction) : Bool := readsSign (operation instruction)

/-- Actual source phase conditions, read from the fixed complete equality pattern. -/
private def phaseEnabled {width : Nat} :
    (instruction : Instruction) → Key width (includeSign instruction) → Bool
  | .remainderSubtract, selected => !first selected
  | .remainderAddback, selected => !first selected && (!second selected || !sign selected)
  | .coefficientSubtract, selected => first selected && (second selected || !sign selected)
  | .coefficientAdd, selected => first selected

/-- Zero-divisor remainder keys emit the identity; coefficient keys retain their source test. -/
def enabled {width : Nat} : (instruction : Instruction) →
    Key width (includeSign instruction) → Bool
  | .remainderSubtract, selected =>
      phaseEnabled .remainderSubtract selected && decide (divisor selected ≠ 0)
  | .remainderAddback, selected =>
      phaseEnabled .remainderAddback selected && decide (divisor selected ≠ 0)
  | .coefficientSubtract, selected => phaseEnabled .coefficientSubtract selected
  | .coefficientAdd, selected => phaseEnabled .coefficientAdd selected

/-- Independent source phase condition before the actual terminal key rejection. -/
private def sourcePhaseEnabled {width : Nat} : Instruction → Registers width → Bool
  | .remainderSubtract, state => !state.flags.first
  | .remainderAddback, state => !state.flags.first && (!state.flags.second || !state.flags.sign)
  | .coefficientSubtract, state => state.flags.first && (state.flags.second || !state.flags.sign)
  | .coefficientAdd, state => state.flags.first

/-- The actual remainder condition also reads the retained nonzero divisor length. -/
def sourceEnabled {width : Nat} (instruction : Instruction) (state : Registers width) : Bool :=
  match instruction with
  | .remainderSubtract | .remainderAddback =>
      sourcePhaseEnabled instruction state && decide (state.divisorLength ≠ 0)
  | .coefficientSubtract | .coefficientAdd => sourcePhaseEnabled instruction state

/-- The phase condition is decoded from actual source bits, rather than supplied externally. -/
theorem enabled_readKey (width : Nat) (instruction : Instruction) (state : Registers width) :
    enabled instruction (readKey width (includeSign instruction) state) =
      sourceEnabled instruction state := by
  cases instruction <;>
    simp only [enabled, phaseEnabled, sourceEnabled, sourcePhaseEnabled, includeSign, operation,
      readsSign, first_readKey, second_readKey, sign_readKey, divisor_readKey]

/-- Internally active frames retain exactly the source arithmetic phase condition. -/
theorem sourceEnabled_active {width : Nat} (instruction : Instruction) (state : Registers width)
    (active : state.divisorLength ≠ 0) :
    sourceEnabled instruction state = sourcePhaseEnabled instruction state := by
  cases instruction with
  | remainderSubtract => rw [sourceEnabled, decide_eq_true active, Bool.and_true]
  | remainderAddback => rw [sourceEnabled, decide_eq_true active, Bool.and_true]
  | coefficientSubtract => rfl
  | coefficientAdd => rfl

/-- A physical zero divisor length rejects both actual remainder bodies, even after low wrap. -/
theorem sourceEnabled_terminal {width : Nat} (instruction : Instruction)
    (remainder : coefficient instruction = false)
    (state : Registers width) (finished : state.divisorLength = 0) :
    sourceEnabled instruction state = false := by
  cases instruction with
  | remainderSubtract =>
      rw [sourceEnabled, decide_eq_false (fun nonzero => nonzero finished), Bool.and_false]
  | remainderAddback =>
      rw [sourceEnabled, decide_eq_false (fun nonzero => nonzero finished), Bool.and_false]
  | coefficientSubtract => cases remainder
  | coefficientAdd => cases remainder

/-- Actual coefficient operand width, with complete high-bit information in phase four. -/
def coefficientRegion (width coefficientLength divisorLength shift : Nat) (deshift : Bool) :
    Option (Window width) :=
  if deshift then
    if fits : divisorLength + shift ≤ width + 3 then
      some (CoefficientWindowOrientation.coefficientWindow width
        (width + 3 - divisorLength - shift) (by omega))
    else none
  else
    if fits : coefficientLength + 1 ≤ width + 3 then
      some (CoefficientWindowOrientation.coefficientWindow width (coefficientLength + 1) fits)
    else none

/-- The static physical window selected by a fixed key, with no finite-field sum truncation. -/
def selectedWindow {width : Nat} (instruction : Instruction)
    (selected : Key width (includeSign instruction)) : Option (Window width) :=
  if coefficient instruction then
    coefficientRegion width (ArithmeticSelectionKey.coefficient selected).toNat
      (divisor selected).toNat (shift selected).toNat (second selected)
  else
    if fits : (ArithmeticSelectionKey.coefficient selected).toNat +
        (quotient selected).toNat + 1 + (shift selected).toNat ≤ width + 3 then
      some (remainderWindow width
        ((ArithmeticSelectionKey.coefficient selected).toNat + (quotient selected).toNat + 1)
        (shift selected).toNat fits)
    else none

/-- The source window directly expressed in the current actual finite register fields. -/
def sourceWindow {width : Nat} (instruction : Instruction) (state : Registers width) :
    Option (Window width) :=
  if coefficient instruction then
    coefficientRegion width state.coefficientLength.toNat state.divisorLength.toNat
      state.shift.toNat state.flags.second
  else
    if fits : state.coefficientLength.toNat + state.quotientLength.toNat + 1 +
        state.shift.toNat ≤ width + 3 then
      some (remainderWindow width
        (state.coefficientLength.toNat + state.quotientLength.toNat + 1) state.shift.toNat fits)
    else none

/-- Exact field decoding gives precisely the same whole physical window and its bounds. -/
theorem selectedWindow_readKey (width : Nat) (instruction : Instruction) (state : Registers width) :
    selectedWindow instruction (readKey width (includeSign instruction) state) =
      sourceWindow instruction state := by
  simp only [selectedWindow, sourceWindow, ArithmeticSelectionKey.coefficient_readKey,
    quotient_readKey, divisor_readKey, shift_readKey, second_readKey]

/-- The actual coefficient-phase branch retains exactly its established fixed physical window. -/
theorem sourceWindow_phaseThree {width : Nat} (instruction : Instruction)
    (oriented : coefficient instruction = true) (state : Registers width)
    (second : state.flags.second = false)
    (fits : state.coefficientLength.toNat + 1 ≤ width + 3) :
    sourceWindow instruction state = some (CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) fits) := by
  unfold sourceWindow
  rw [oriented]
  change coefficientRegion width state.coefficientLength.toNat state.divisorLength.toNat
    state.shift.toNat state.flags.second = _
  rw [second]
  change (if bound : state.coefficientLength.toNat + 1 ≤ width + 3 then
    some (CoefficientWindowOrientation.coefficientWindow width
      (state.coefficientLength.toNat + 1) bound) else none) = _
  rw [dif_pos fits]

/-- Phase four reads every aligned coefficient bit, excluding the actual divisor and fraction. -/
theorem sourceWindow_phaseFour {width : Nat} (instruction : Instruction)
    (oriented : coefficient instruction = true) (state : Registers width)
    (second : state.flags.second = true)
    (fits : state.divisorLength.toNat + state.shift.toNat ≤ width + 3) :
    sourceWindow instruction state = some (CoefficientWindowOrientation.coefficientWindow width
      (width + 3 - state.divisorLength.toNat - state.shift.toNat) (by omega)) := by
  unfold sourceWindow
  rw [oriented]
  change coefficientRegion width state.coefficientLength.toNat state.divisorLength.toNat
    state.shift.toNat state.flags.second = _
  rw [second]
  change (if bound : state.divisorLength.toNat + state.shift.toNat ≤ width + 3 then
    some (CoefficientWindowOrientation.coefficientWindow width
      (width + 3 - state.divisorLength.toNat - state.shift.toNat) (by omega)) else none) = _
  rw [dif_pos fits]

private def identity (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.identity (Qubits (encoding width).width) (List.range (encoding width).width)
    List.nodup_range

private theorem identity_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (identity width) id :=
  UnitaryCircuit.Realizes.identityAt (encoding width) (List.range (encoding width).width)
    List.nodup_range

/-- Execute the actual selector at a valid enabled static key, otherwise the actual identity. -/
def program (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  if enabled instruction selected then
    match selectedWindow instruction selected with
    | some window => ArithmeticSelector.program window (operation instruction)
        (coefficient instruction) selected
    | none => identity width
  else identity width

/-- Exact complete-frame action of that same actual static native program. -/
def step (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width) : Registers width :=
  if enabled instruction selected then
    match selectedWindow instruction selected with
    | some window => ArithmeticSelector.step window (operation instruction)
        (coefficient instruction) selected state
    | none => state
  else state

/-- The actual fixed-key instruction realizes its full action for arbitrary input Ctrl and Iter. -/
theorem program_realizes (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) :
    UnitaryCircuit.Realizes (encoding width) (program width instruction selected)
      (step width instruction selected) := by
  unfold program step
  split
  · cases choice : selectedWindow instruction selected with
    | none => exact identity_realizes width
    | some window => exact ArithmeticSelector.program_realizes window _ _ selected
  · exact identity_realizes width

/-- The unique matched key's ungated body, with actual phase and physical-window checks. -/
def selectedBody (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width) : Registers width :=
  if enabled instruction selected then
    match selectedWindow instruction selected with
    | some window => ArithmeticSelector.bodyStep window (operation instruction)
        (coefficient instruction) state
    | none => state
  else state

/-- The independent current-frame source operation, including its physical-window boundary. -/
def sourceStep {width : Nat} (instruction : Instruction) (state : Registers width) :
    Registers width :=
  if sourceEnabled instruction state then
    match sourceWindow instruction state with
    | some window => ArithmeticSelector.bodyStep window (operation instruction)
        (coefficient instruction) state
    | none => state
  else state

/-- The actual key's chosen body equals the independent current-field source action. -/
theorem selectedBody_readKey (width : Nat) (instruction : Instruction) (state : Registers width) :
    selectedBody width instruction (readKey width (includeSign instruction) state) state =
      sourceStep instruction state := by
  simp only [selectedBody, sourceStep, enabled_readKey, selectedWindow_readKey]

/-- Every static instruction restores its incoming Ctrl on every frame. -/
theorem step_control (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width) :
    (step width instruction selected state).control = state.control := by
  unfold step
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window => exact ArithmeticSelector.step_control window _ _ selected state
  · rfl

/-- The actual static instruction restores arbitrary Iter on its active and inactive branches. -/
theorem step_iteration (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width) :
    (step width instruction selected state).flags.iteration = state.flags.iteration := by
  unfold step
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window => exact ArithmeticSelector.step_iteration window _ _ selected state
  · rfl

/-- Every later selector sees precisely the same actual source key after this instruction. -/
theorem step_readKey (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width) :
    readKey width (includeSign instruction) (step width instruction selected state) =
      readKey width (includeSign instruction) state := by
  unfold step
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window => exact ArithmeticSelector.step_readKey window _ _ selected state
  · rfl

/-- Every nonmatching static key is inactive when Ctrl has been initialized by the algorithm. -/
theorem step_inactive (width : Nat) (instruction : Instruction)
    (selected : Key width (includeSign instruction)) (state : Registers width)
    (clean : state.control = false)
    (different : selected ≠ readKey width (includeSign instruction) state) :
    step width instruction selected state = state := by
  unfold step
  split
  · cases choice : selectedWindow instruction selected with
    | none => rfl
    | some window =>
        exact ArithmeticSelector.step_inactive window _ _ selected state clean different
  · rfl

/-- The actual matching selector executes its enabled body once, with complete predicate cleanup. -/
theorem step_matching (width : Nat) (instruction : Instruction) (state : Registers width)
    (clean : state.control = false) :
    step width instruction (readKey width (includeSign instruction) state) state =
      selectedBody width instruction (readKey width (includeSign instruction) state) state := by
  unfold step selectedBody
  split
  · cases choice : selectedWindow instruction (readKey width (includeSign instruction) state) with
    | none => rfl
    | some window => exact ArithmeticSelector.step_matching window _ _ state clean
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticInstruction
