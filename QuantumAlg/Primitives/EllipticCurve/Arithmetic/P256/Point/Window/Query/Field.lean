/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Effect
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Arithmetic

/-!
# Original field value of the concrete selected table addition

The finite-word output is the ordinary residue of its original target plus
the actually selected table column. The selector is the original complete
digit and, for the exceptional occurrence, the independent genuine normal
bit. These equations translate actual numerical endpoints to the independent
chronological field schedule; they introduce no arithmetic instructions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

variable (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (exceptional : Bool)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ 256)) (state : Raw)
    (column target : ZMod modulus)

/-- The concrete target word represents its ordinary selected field addition. -/
lemma queryValue_word
    (sourceValue : selectedWord stream width bounded table state = Residue.word column)
    (targetValue : ports.target.value state.1 = Residue.word target) :
    queryValue stream width bounded ports exceptional table state =
      Residue.word
        (target + if querySelected stream width bounded exceptional state then column else 0) := by
  unfold queryValue
  rw [sourceValue, targetValue]
  cases selected : querySelected stream width bounded exceptional state with
  | false => simp only [Bool.false_eq_true, if_false, add_zero]
  | true =>
      simp only [if_true, Residue.sum_word]
      exact congrArg Residue.word (add_comm column target)

/-- The original cleared query label changes just the target to this same field value. -/
lemma query_cleared_word (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (exceptional : Bool)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ 256))
    (state : Raw) (column target : ZMod modulus) (clean : Frame.CleanPool state.1)
    (zero : ∀ index, ((resultWord ports.source).bit index).get state = false)
    (sourceValue : selectedWord stream (highRemaining + lowWidth) bounded table state =
      Residue.word column)
    (targetValue : ports.target.value state.1 = Residue.word target) :
    let loaded :=
      loadedState stream ports.source highRemaining lowWidth bounded lowBound table state
    resultSetConstant (resultWord ports.source) 0
        (if exceptional then exceptionalStep stream (highRemaining + lowWidth) bounded ports loaded
          else ordinaryStep stream (highRemaining + lowWidth) bounded ports loaded) =
      resultSetConstant (resultWord ports.target)
        (Residue.word (target +
          if querySelected stream (highRemaining + lowWidth) bounded exceptional state then column
            else 0)) state := by
  dsimp only
  rw [query_cleared_eq_target_set stream highRemaining lowWidth bounded lowBound ports exceptional
    table state clean zero, queryValue_word stream _ bounded ports exceptional table state
      column target sourceValue targetValue]

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
