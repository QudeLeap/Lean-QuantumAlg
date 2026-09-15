/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program.Readout
import all QuantumAlg.Util.RSA.Quadratic.Selection

/-!
# Actual persistent output equals the original quadratic source result

The flag and word read from the actual returned store encode an optional
factor. An earlier stored factor has priority. Otherwise this output is the
original recoverFactorFromShortLog result passed through the circuit's real
word conversion. At the original modulus-capacity boundary that conversion
is exact, since every accepted source factor is strictly below the modulus.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width resultWidth : Nat}

/-- Read the actual persistent acceptance flag and its full stored factor word. -/
def selectedFactor (original : FirstAccepted.Refs ctx resultWidth) (store : Store ctx) :
    Option Nat :=
  if (store.read (FirstAccepted.cellRead original.accepted)).toBool then
    some (store.read (FirstAccepted.cellRead original.selected)).toNat else none

private theorem observed_order (accepted firstValid secondValid : Bool) (first second : Nat)
    (old : CShape.Value (.unsignedWord resultWidth)) :
    (if accepted || (firstValid || secondValid) then
      some ((if accepted then old else if firstValid then CShape.wordOfNat resultWidth first
        else if secondValid then CShape.wordOfNat resultWidth second else old).toNat)
    else none) =
      (if accepted then some old.toNat else none).orElse (fun _ =>
        (if firstValid then some first else if secondValid then some second else none).map
          (fun factor => factor % 2 ^ resultWidth)) := by
  cases accepted <;> cases firstValid <;> cases secondValid <;> rfl

/-- The same complete native execution returns the first original factor with actual conversion. -/
theorem nativeQuadratic_program_source
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (unique : ([original.take.key, original.available.key, original.selected.key,
      original.accepted.key] : List StorageKey).Nodup) (store : Store ctx) :
    selectedFactor original (programStep input modulus original store).1 =
      (selectedFactor original store).orElse (fun _ =>
        (RSA.recoverFactorFromShortLog (store.read modulus).toNat (store.read input).toNat).map
          (fun factor => factor % 2 ^ resultWidth)) := by
  let source := RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat
  let firstValid := decide (1 < source.1 ∧ source.1 < (store.read modulus).toNat ∧
    (store.read modulus).toNat % source.1 = 0)
  let secondValid := decide (1 < source.2 ∧ source.2 < (store.read modulus).toNat ∧
    (store.read modulus).toNat % source.2 = 0)
  have actual := nativeQuadratic_program_latches input modulus original unique store
  have observed := congrArg₂
    (fun (accepted : Bool) (word : CShape.Value (.unsignedWord resultWidth)) =>
      if accepted then some word.toNat else none) actual.1 actual.2
  refine observed.trans ((observed_order
    (store.read (FirstAccepted.cellRead original.accepted)).toBool firstValid secondValid
    source.1 source.2 (store.read (FirstAccepted.cellRead original.selected))).trans ?_)
  exact congrArg (fun result : Option Nat =>
    (selectedFactor original store).orElse (fun _ => result.map
      (fun factor => factor % 2 ^ resultWidth)))
    (RSA.recoverFactorFromShortLog_eq_decisions
      (store.read modulus).toNat (store.read input).toNat).symm

/-- The original modulus-capacity fact removes exactly the real word conversion, with no new
initialization or candidate-capacity condition. -/
theorem nativeQuadratic_program_source_exact
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (unique : ([original.take.key, original.available.key, original.selected.key,
      original.accepted.key] : List StorageKey).Nodup) (store : Store ctx)
    (capacity : (store.read modulus).toNat ≤ 2 ^ resultWidth) :
    selectedFactor original (programStep input modulus original store).1 =
      (selectedFactor original store).orElse (fun _ =>
        RSA.recoverFactorFromShortLog (store.read modulus).toNat (store.read input).toNat) :=
  (nativeQuadratic_program_source input modulus original unique store).trans
    (congrArg (fun result : Option Nat => (selectedFactor original store).orElse (fun _ => result))
      (RSA.recoverFactorFromShortLog_map_mod
        (store.read modulus).toNat (store.read input).toNat resultWidth capacity))

/-- Actual allocation supplies the persistent selector's positions for the source result. -/
theorem nativeQuadratic_allocated_program_source
    (input : CInputRef (SelectionLayout.context ctx resultWidth) (.unsignedWord width))
    (modulus : CInputRef (SelectionLayout.context ctx resultWidth)
      (.unsignedWord (RSA.quadraticWordWidth width)))
    (store : Store (SelectionLayout.context ctx resultWidth)) :
    let original := SelectionLayout.refs ctx resultWidth
    selectedFactor original (programStep input modulus original store).1 =
      (selectedFactor original store).orElse (fun _ =>
        (RSA.recoverFactorFromShortLog (store.read modulus).toNat (store.read input).toNat).map
          (fun factor => factor % 2 ^ resultWidth)) :=
  nativeQuadratic_program_source input modulus (SelectionLayout.refs ctx resultWidth)
    (SelectionLayout.nativeRecovery_selection_nodup ctx resultWidth) store

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
