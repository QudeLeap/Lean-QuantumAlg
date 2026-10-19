/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout
import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Actual initialization of the finite recovery cursor

The decoder reads the fresh false accepted latch followed by the real sampled
phase bits, directly materializing the widened numerator. The literal loader
materializes the dyadic denominator with actual shifts and increments. Two
increments initialize the older continuant and modular one; negating the still
false accepted latch activates the first cursor visit. Every width follows
the same circuit, with no sentinel branch or temporary decoded word.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

/-- Actual source bits prefixed by the real fresh false accepted latch. -/
def initialPhaseBitRefs (ctx : RuntimeCtx kind) (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) :
    Fin (phaseBits + 1) → CInputRef (recoveryContext ctx modulusWidth (phaseBits + 1)) .bit :=
  Fin.cons (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)
    (fun index => .bitsGet
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields sample) index)

/-- The existing decoder writes the widened numerator from those actual bit references. -/
def decodeInitialNumerator {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) :
    Circuit model (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  TerminalDecode.intoFromBitRefs (model := model) .bigEndian
    (initialPhaseBitRefs ctx modulusWidth phaseBits sample)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator

/-- Increment the genuinely fresh zero older-continuant denominator. -/
def initializeOlderOp (ctx : RuntimeCtx kind) (modulusWidth phaseBits : Nat) :
    ClassicalOp (.unsignedWord (phaseBits + 1)) (.unsignedWord (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .wordUnary .increment (phaseBits + 1) _
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older

/-- Increment the actual modular-one workspace word. -/
def initializeOneOp (ctx : RuntimeCtx kind) (modulusWidth phaseBits : Nat) :
    ClassicalOp (.unsignedWord modulusWidth) (.unsignedWord modulusWidth)
      (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .wordUnary .increment modulusWidth _
    (recoveryCells ctx modulusWidth (phaseBits + 1)).one
    (recoveryFieldCell ctx modulusWidth (phaseBits + 1) recoveryFields 1)

/-- The actual false accepted latch supplies the activation instruction. -/
def initializeActiveOp (ctx : RuntimeCtx kind) (modulusWidth phaseBits : Nat) :
    ClassicalOp .bit .bit (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .bit .not _ (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.active

/-- Complete actual cursor initialization after the genuine field allocations. -/
def initializeScan {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) :
    Circuit model (recoveryContext ctx modulusWidth (phaseBits + 1))
      (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  .seq (decodeInitialNumerator (model := model) ctx modulusWidth phaseBits sample)
    (.seq (ConstantWord.circuit (model := model)
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator
      (2 ^ phaseBits))
      (.seq (BitWord.instruction (execution := model)
          (initializeOlderOp ctx modulusWidth phaseBits))
        (.seq (BitWord.instruction (execution := model)
          (initializeOneOp ctx modulusWidth phaseBits))
          (BitWord.instruction (execution := model)
          (initializeActiveOp ctx modulusWidth phaseBits)))))

/-- Concrete initial store and the real decoder, loader and elementary initialization paths. -/
def initializeScanStep {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    Store (recoveryContext ctx modulusWidth (phaseBits + 1)) ×
      (initializeScan (model := model) ctx modulusWidth phaseBits sample).Path :=
  let decoded := TerminalDecode.foldStep (model := model)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator
    (List.ofFn (initialPhaseBitRefs ctx modulusWidth phaseBits sample)) store
  let loaded := ConstantWord.foldStep (model := model)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator
    (List.ofFn (ConstantWord.constantBits (phaseBits + 1) (2 ^ phaseBits))) decoded.1
  let older := BitWord.instructionStep (execution := model)
    (initializeOlderOp ctx modulusWidth phaseBits) loaded.1
  let one := BitWord.instructionStep (execution := model)
    (initializeOneOp ctx modulusWidth phaseBits) older.1
  let active := BitWord.instructionStep (execution := model)
    (initializeActiveOp ctx modulusWidth phaseBits) one.1
  (active.1, (decoded.2, (loaded.2, (older.2, (one.2, active.2)))))

/-- The one actual interpreter executes exactly those initialization records on every full block. -/
lemma nativeRecovery_initialize_execute {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (recoveryContext ctx modulusWidth (phaseBits + 1))
      Reference (model.HiddenState × History)) :
    (initializeScan (model := model) ctx modulusWidth phaseBits sample).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        ((initializeScanStep (model := model) ctx modulusWidth phaseBits sample entry.1).1,
          (entry.2.1, (entry.2.2,
            (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
              entry.1).2)))) := by
  simp only [initializeScan, decodeInitialNumerator, TerminalDecode.intoFromBitRefs,
    TerminalDecode.sourceIndex, ConstantWord.circuit, Circuit.execute_seq,
    TerminalDecode.terminalDecode_fold_execute, ConstantWord.constantWord_fold_execute,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
