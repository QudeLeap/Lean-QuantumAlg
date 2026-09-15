/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initialization.Laws
import all QuantumAlg.Components.Classical.OrderRecovery.Native.SourceValidation

/-!
# Source cursor observations of the actual recovery store

These propositions relate the four real cursor reads and two actual latches
to the original mathematical Euclidean cursor. They do not execute a second
machine. The genuine initialization proves the initial relation from the
stored source input, including all widths admitted by the original modulus.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The four actual word reads represent the original mathematical cursor coordinates. -/
structure CursorReads {width : Nat} (cells : CursorCells ctx width) (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor) : Prop where
  /-- Actual Euclidean numerator. -/
  numerator : (store.read (cellRead cells.numerator)).toNat = cursor.numerator
  /-- Actual Euclidean denominator. -/
  denominator : (store.read (cellRead cells.denominator)).toNat = cursor.denominator
  /-- Actual older continuant denominator. -/
  older : (store.read (cellRead cells.older)).toNat = cursor.older.denominator
  /-- Actual previous continuant denominator. -/
  previous : (store.read (cellRead cells.previous)).toNat = cursor.previous.denominator

/-- A still-unaccepted real scan store tracks the source cursor and its actual activity bit. -/
structure PendingCursorReads (cells : ScanCells ctx modulusWidth (phaseBits + 1))
    (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor) : Prop
    extends CursorReads cells.cursor store cursor where
  /-- The actual activity latch agrees with the source nonzero-divisor test. -/
  active : store.read (cellRead cells.cursor.active) = .bit cursor.active
  /-- No candidate has yet been copied into the accepted-result latch. -/
  accepted : store.read (cellRead cells.accepted) = .bit false

/-- The real validation inputs contain the source base and both initialized constants. -/
structure ScanSourceReads
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx) : Prop where
  /-- The original stored base retains its exact source encoding. -/
  baseValue : store.read base = .canonicalResidue input.base
  /-- The zero comparison operand is still the actual zero word. -/
  zeroValue : (store.read cells.zero).toNat = 0
  /-- The modular-return comparison operand is the actual word one. -/
  oneValue : (store.read cells.one).toNat = 1

/-- The actual initialization establishes the source cursor without an initialization premise. -/
theorem nativeRecovery_initialized_cursor
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    (sampleValue : store.read sample = .bits input.terminalBits) :
    PendingCursorReads (recoveryCells ctx modulusWidth (phaseBits + 1))
      (initializeScanStep ctx modulusWidth phaseBits sample
        (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1
      (.initial (ClassicalAlgorithms.OrderRecovery.decodedIndex input).val
        (2 ^ phaseBits)) := by
  have capacity : 1 < 2 ^ (phaseBits + 1) := by
    rw [Nat.pow_succ]
    have positive := Nat.two_pow_pos phaseBits
    omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have actual := nativeRecovery_initialized_numerator modulusWidth phaseBits sample store
    rw [sampleValue] at actual
    exact actual
  · exact nativeRecovery_initialized_denominator modulusWidth phaseBits sample store
  · change ((initializeScanStep ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older)).toNat = 1
    have actual := congrArg CShape.Value.toNat
      (nativeRecovery_initialized_older modulusWidth phaseBits sample store)
    simpa only [CShape.wordOfNat_val, CShape.wordModulus, Nat.mod_eq_of_lt capacity] using actual
  · have actual := nativeRecovery_initialize_unwritten_field modulusWidth phaseBits sample store
      5 (by decide)
    exact congrArg CShape.Value.toNat actual
  · have actual := nativeRecovery_initialized_active modulusWidth phaseBits sample store
    have active :
        (ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor.initial
          (ClassicalAlgorithms.OrderRecovery.decodedIndex input).val
          (2 ^ phaseBits)).active = true := by
      exact decide_eq_true (Nat.two_pow_pos phaseBits).ne'
    rw [active]
    exact actual
  · exact nativeRecovery_initialize_unwritten_field modulusWidth phaseBits sample store
      9 (by decide)

/-- The actual initialization establishes the source base and comparison operands. -/
theorem nativeRecovery_initialized_source_reads
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    (baseValue : store.read base = .canonicalResidue input.base) :
    ScanSourceReads spec input
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
      (initializeScanStep ctx modulusWidth phaseBits sample
        (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (nativeRecovery_initialize_read_original modulusWidth phaseBits sample store base).trans
      baseValue
  · exact congrArg CShape.Value.toNat
      (nativeRecovery_initialize_unwritten_field modulusWidth phaseBits sample store 0 (by decide))
  · have capacity : 1 < 2 ^ modulusWidth :=
      (ClassicalAlgorithms.Modular.modulusSpec_one_lt spec.modulusSpec).trans_le
        spec.modulusSpec.le_capacity
    have actual := congrArg CShape.Value.toNat
      (nativeRecovery_initialized_one modulusWidth phaseBits sample store)
    simpa only [CShape.wordOfNat_val, CShape.wordModulus, Nat.mod_eq_of_lt capacity] using actual

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
