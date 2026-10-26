/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Selection
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Update
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber.Set

/-!
# Original-label result of one real table arithmetic query

The native body uses the original digit predicate, normal bit, full-address
table value and original numerical target. Clearing the original loaded
word after this action leaves exactly one target-word replacement in the
complete original label. This mathematical endpoint discharges the output
label in the separately proved actual per-record coherent query law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

/-- The original complete digit and independent normal bit select the numerical addition. -/
def querySelected (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (exceptional : Bool) (state : Raw) : Bool :=
  let selected := !decide (∀ index, (Enable.digitBit stream width bounded index).get state = false)
  if exceptional then selected && !normalBit.get state else selected

/-- Independent numerical output from the original digit, full table address and target. -/
def queryValue (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (exceptional : Bool)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ 256)) (state : Raw) : Word :=
  if querySelected stream width bounded exceptional state then
    ModularAddition.modularSumWord (selectedWord stream width bounded table state)
      (ports.target.value state.1)
    else ports.target.value state.1

/-- The retained arithmetic enable reads exactly the original, unchanged complete digit. -/
lemma loaded_arithmeticSource_selected (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256))
    (state : Raw) (clean : Frame.CleanPool state.1) :
    let loaded :=
      loadedState stream ports.source highRemaining lowWidth bounded lowBound table state
    (Native.BorrowedControl.controlBit ports).get
        ((Placement.layout ports).grouping
          (arithmeticSource stream (highRemaining + lowWidth) bounded loaded)).2.2 =
      !decide (∀ index,
        (Enable.digitBit stream (highRemaining + lowWidth) bounded index).get state = false) := by
  have actual := arithmeticSource_selected stream (highRemaining + lowWidth) bounded ports
    (loadedState stream ports.source highRemaining lowWidth bounded lowBound table state)
    (loadedState_cleanPool stream ports.source highRemaining lowWidth bounded lowBound table
      state clean)
  simpa only [loadedState_digit] using actual

/-- Both actual body-coordinate endpoints change only the original numerical target. -/
lemma loadedBody_eq_target_set (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (exceptional : Bool)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256))
    (state : Raw) (clean : Frame.CleanPool state.1)
    (zero : ∀ index, ((resultWord ports.source).bit index).get state = false) :
    let loaded :=
      loadedState stream ports.source highRemaining lowWidth bounded lowBound table state
    (if exceptional then exceptionalStep stream (highRemaining + lowWidth) bounded ports loaded
      else ordinaryStep stream (highRemaining + lowWidth) bounded ports loaded) =
        resultSetConstant (resultWord ports.target)
          (queryValue stream (highRemaining + lowWidth) bounded ports exceptional table state)
          loaded := by
  let loaded := loadedState stream ports.source highRemaining lowWidth bounded lowBound table state
  have pool : Frame.CleanPool loaded.1 :=
    loadedState_cleanPool stream ports.source highRemaining lowWidth bounded lowBound table
      state clean
  have selected := loaded_arithmeticSource_selected stream highRemaining lowWidth bounded lowBound
    ports table state clean
  have source : ports.source.value (arithmeticSource stream (highRemaining + lowWidth)
      bounded loaded) = selectedWord stream (highRemaining + lowWidth) bounded table state :=
    (arithmeticSource_word stream _ bounded ports.source loaded).trans
      (loadedState_source stream ports.source highRemaining lowWidth bounded lowBound table state
        zero)
  have target : ports.target.value (arithmeticSource stream (highRemaining + lowWidth)
      bounded loaded) = ports.target.value state.1 :=
    (arithmeticSource_word stream _ bounded ports.target loaded).trans
      (loadedState_word_other stream ports.source ports.target ports.source_target highRemaining
        lowWidth bounded lowBound table state)
  have normal : (Native.controlBit ports .normal).get
      ((Placement.layout ports).grouping
        (arithmeticSource stream (highRemaining + lowWidth) bounded loaded)).2.2 =
      normalBit.get state :=
    (arithmeticSource_normal stream _ bounded ports loaded).trans
      (loadedState_normal stream ports.source highRemaining lowWidth bounded lowBound table state)
  cases exceptional with
  | false =>
      have actual := ordinaryStep_eq_target_set stream (highRemaining + lowWidth) bounded
        ports loaded pool
      dsimp only at actual
      rw [selected, source, target] at actual
      exact actual
  | true =>
      have actual := exceptionalStep_eq_target_set stream (highRemaining + lowWidth) bounded
        ports loaded pool
      dsimp only at actual
      rw [selected, normal, source, target] at actual
      exact actual

/-- Real same-word clearing leaves exactly one target change in the complete original label. -/
lemma query_cleared_eq_target_set (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (exceptional : Bool)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256))
    (state : Raw) (clean : Frame.CleanPool state.1)
    (zero : ∀ index, ((resultWord ports.source).bit index).get state = false) :
    let loaded :=
      loadedState stream ports.source highRemaining lowWidth bounded lowBound table state
    resultSetConstant (resultWord ports.source) 0
        (if exceptional then exceptionalStep stream (highRemaining + lowWidth) bounded ports loaded
          else ordinaryStep stream (highRemaining + lowWidth) bounded ports loaded) =
      resultSetConstant (resultWord ports.target)
        (queryValue stream (highRemaining + lowWidth) bounded ports exceptional table state)
        state := by
  let loaded := loadedState stream ports.source highRemaining lowWidth bounded lowBound table state
  have body := loadedBody_eq_target_set stream highRemaining lowWidth bounded lowBound ports
    exceptional table state clean zero
  change resultSetConstant (resultWord ports.source) 0
      (if exceptional then exceptionalStep stream (highRemaining + lowWidth) bounded ports loaded
        else ordinaryStep stream (highRemaining + lowWidth) bounded ports loaded) = _
  rw [body, resultSetConstant_comm_of_disjoint encoding_surjective
    (resultWord ports.source) (resultWord ports.target) (resultWord_distinct ports.source)
    (resultWord_distinct ports.target)
    (resultWord_ports_disjoint ports.source ports.target ports.source_target)]
  have cleared : resultSetConstant (resultWord ports.source) 0 loaded = state :=
    resultSetConstant_zero_xor encoding_surjective (resultWord ports.source)
      (resultWord_distinct ports.source) _ state zero
  rw [cleared]

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
