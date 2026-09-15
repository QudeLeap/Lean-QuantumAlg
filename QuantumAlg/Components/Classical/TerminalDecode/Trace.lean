/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Resources

/-!
# Independent native trace of each actual selected decoder path

Every bit emits a shift and emits an increment precisely in the selected true
arm. The independent list formula retains the order and width of both native
operations, so its pool and event count are derived from the actual interpreter.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent chronological native formula for one selected source bit. -/
def bitTrace (width : Nat) (bit : Bool) : List (Resource.Event kind) :=
  [shiftEvent width] ++ if bit then [incrementEvent width] else []

/-- Independent chronological native formula for an ordered list of selected source bits. -/
def bitsTrace (width : Nat) (bits : List Bool) : List (Resource.Event kind) :=
  (bits.map (bitTrace width)).flatten

/-- Ordered actual classical branch values present in a decoder fold's path. -/
def selectedBits (output : CWriteRef ctx (OutputShape width)) :
    (inputs : List (CInputRef ctx .bit)) → (foldBitRefs output inputs).Path → List Bool
  | [], _ => []
  | _input :: rest, path => path.1.2.1.toBool :: selectedBits output rest path.2

/-- Every actual native bit append emits its exact independent selected-bit formula. -/
theorem bitRef_events (input : CInputRef ctx .bit) (output : CWriteRef ctx (OutputShape width))
    (path : (bitRefRoutine input output).Path) :
    (bitRefRoutine input output).eventTrace path = bitTrace width path.2.1.toBool := by
  rcases path with ⟨shiftPath, value, branchPath⟩
  cases value with
  | bit bit => cases bit <;> rfl

/-- Every actual complete decoder path emits the independent ordered native bit formula. -/
theorem fold_events (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (path : (foldBitRefs output inputs).Path) :
    (foldBitRefs output inputs).eventTrace path =
      bitsTrace width (selectedBits output inputs path) := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
    change _ ++ _ = _
    rw [bitRef_events, ih]
    rfl

/-- Actual branch selections contain exactly one bit per supplied source reference. -/
theorem selectedBits_length (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (path : (foldBitRefs output inputs).Path) :
    (selectedBits output inputs path).length = inputs.length := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => exact congrArg Nat.succ (ih path.2)

/-- Independent native decoding emits at most two operations for each selected source bit. -/
theorem bitsTrace_length_le (width : Nat) (bits : List Bool) :
    (bitsTrace (kind := kind) width bits).length ≤ 2 * bits.length := by
  induction bits with
  | nil => exact le_rfl
  | cons bit rest ih =>
    have count : (bitTrace (kind := kind) width bit).length ≤ 2 := by
      cases bit <;> simp [bitTrace]
    change ((bitTrace width bit) ++ bitsTrace width rest).length ≤ _
    rw [List.length_append, List.length_cons]
    omega

/-- Every actual bit fold obeys the independent two-native-operations-per-bit count. -/
theorem fold_eventCount_le (output : CWriteRef ctx (OutputShape width))
    (inputs : List (CInputRef ctx .bit)) (path : (foldBitRefs output inputs).Path) :
    ((foldBitRefs output inputs).eventTrace path).length ≤ 2 * inputs.length := by
  rw [fold_events]
  exact (bitsTrace_length_le width _).trans_eq (congrArg (2 * ·)
    (selectedBits_length output inputs path))

end QuantumAlg.ClassicalRoutines.TerminalDecode
