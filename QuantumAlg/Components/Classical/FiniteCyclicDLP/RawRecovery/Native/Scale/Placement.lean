/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual lexical frequency-scaling circuit

Three fresh cells store the denominator, full product and division outputs.
The original denominator loader increments its freshly initialized zero word
and shifts left exactly the raw width. The full-width scaling instructions
then write the existing output, after which all three scratch cells are popped.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

section Placement

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- First lexical cell can represent the exact power-of-two denominator. -/
@[reducible] def scaleDenominatorCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh

/-- Second lexical cell retains every bit of the original product. -/
@[reducible] def scaleProductCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (scaleDenominatorCtx ctx width).addWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
    (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh

/-- Final lexical cell retains both complete division results. -/
@[reducible] def scaleCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (scaleProductCtx ctx width).addWorkspace (scaleProductCtx ctx width).canonicalFreshKey
    (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- Original structural inputs retain their identities under all three scratch scopes. -/
def underScale {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (scaleCtx ctx width) shape :=
  ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1)))
      (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
        (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- The same actual existing output remains writable under the three fresh scopes. -/
def writeUnderScale {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (scaleCtx ctx width) shape :=
  ((output.underWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1)))
      (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
        (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- First lexical head, lifted through the two later allocations. -/
def scaleDenominatorCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (scaleCtx ctx width) (.unsignedWord (width + 1)) :=
  ((CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).underWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1)))
      (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).underWorkspace
        (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
        (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- Second lexical head, lifted past the actual division-results allocation. -/
def scaleProductCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (scaleCtx ctx width) (.unsignedWord (width + (width + 1))) :=
  (CWriteRef.workspaceHead (scaleDenominatorCtx ctx width)
    (scaleDenominatorCtx ctx width).canonicalFreshKey (.unsignedWord (width + (width + 1)))
    (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).underWorkspace
      (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
      (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- Actual final lexical head for the complete quotient and remainder. -/
def scaleDivisionCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (scaleCtx ctx width) (scaleDivisionShape width) :=
  CWriteRef.workspaceHead (scaleProductCtx ctx width) (scaleProductCtx ctx width).canonicalFreshKey
    (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- Store obtained by precisely the three actual lexical entries. -/
def enterScale (store : Store ctx) (width : Nat) : Store (scaleCtx ctx width) :=
  ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1))
    ctx.canonicalFreshKey_fresh).pushWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1)))
      (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh).pushWorkspace
        (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
        (scaleProductCtx ctx width).canonicalFreshKey_fresh

/-- Release the three exact scratch heads, in the actual reverse allocation order. -/
def leaveScale (store : Store (scaleCtx ctx width)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
      (Store.popWorkspace (scaleProductCtx ctx width).canonicalFreshKey (scaleDivisionShape width)
        (scaleProductCtx ctx width).canonicalFreshKey_fresh store))

end Placement

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original denominator loading: one increment and exactly the raw width's shifts. -/
def scaleSeed (denominator : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (Word.PowerOfTwo.incrementOp denominator))
    (Word.PowerOfTwo.shiftInto (model := model) width denominator)

/-- Actual denominator-loading store and its full native path. -/
def scaleSeedStep (denominator : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (scaleSeed (model := model) denominator).Path :=
  let first := BitWord.instructionStep (execution := model)
    (Word.PowerOfTwo.incrementOp denominator) store
  let shifted := Word.PowerOfTwo.shiftStep (model := model) width denominator first.1
  (shifted.1, (first.2, shifted.2))

/-- The real loader preserves the persistent service and all quantum-reference blocks. -/
theorem scaleSeed_execute (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scaleSeed (model := model) denominator).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scaleSeedStep (model := model) denominator entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.incrementOp denominator))
    (Word.PowerOfTwo.shiftInto (model := model) width denominator)
    (fun before =>
      let result := BitWord.instructionStep (execution := model)
        (Word.PowerOfTwo.incrementOp denominator) before.1
      ((result.1, before.2), result.2))
    (fun before =>
      let result := Word.PowerOfTwo.shiftStep (model := model) width denominator before.1
      ((result.1, before.2), result.2)) ?_ ?_ Reference state).trans ?_
  · intro reference history _ initial
    exact (BitWord.bitWord_instruction_execute (execution := model)
      (Word.PowerOfTwo.incrementOp denominator) initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history _ initial
    exact (Word.PowerOfTwo.shiftInto_execute (model := model) width denominator
      reference initial).trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Scope initialization supplies this local zero premise; no old caller cell is constrained. -/
theorem scaleSeed_zero_value (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) (initial : (store.read (scaleRead denominator)).toNat = 0) :
    ((scaleSeedStep (model := model) denominator store).1.read (scaleRead denominator)).toNat =
      2 ^ width := by
  have increment : ((store.applyOp (Word.PowerOfTwo.incrementOp denominator)).read
      (scaleRead denominator)).toNat = 1 := by
    simp only [scaleRead, Store.applyOp, Word.PowerOfTwo.incrementOp, ClassicalOp.outputRef,
      Store.read_write_same, ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
    change ((store.read (scaleRead denominator)).toNat + 1) % 2 ^ (width + 1) = 1
    rw [initial, Nat.zero_add, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have capacity : 2 ^ width < 2 ^ (width + 1) := by
    rw [pow_succ]
    have positive := Nat.two_pow_pos width
    omega
  have shifted := Word.PowerOfTwo.shiftInto_read width denominator
    (store.applyOp (Word.PowerOfTwo.incrementOp denominator))
  exact shifted.trans ((congrArg (fun value => (value * 2 ^ width) % 2 ^ (width + 1))
    increment).trans (by rw [Nat.one_mul, Nat.mod_eq_of_lt capacity]))

/-- Loading the denominator preserves every structural read outside that actual scratch cell. -/
theorem scaleSeed_read_other (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : denominator.key ∉ other.storageKeys) :
    (scaleSeedStep (model := model) denominator store).1.read other = store.read other :=
  (Word.PowerOfTwo.shiftInto_callerFrame width denominator _ other separate).trans
    (Store.read_applyOp_of_not_mem_storageKeys store
      (Word.PowerOfTwo.incrementOp denominator) other separate)

/-- Actual three arithmetic instructions placed on these exact scratch and caller cells. -/
def scalePlaced (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (scaleCtx ctx width) (scaleCtx ctx width) :=
  scaleBody (model := model) (underScale raw width) (underScale modulus width)
    (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
    (scaleDivisionCell ctx width) (writeUnderScale output width)

/-- The actual denominator is loaded before the first full-width arithmetic instruction. -/
def scalePrepared (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (scaleCtx ctx width) (scaleCtx ctx width) :=
  .seq (scaleSeed (model := model) (scaleDenominatorCell ctx width))
    (scalePlaced (model := model) raw modulus output)

/-- Complete inner store and original chronological loader-and-arithmetic path. -/
def scalePreparedStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (scaleCtx ctx width)) :
    Store (scaleCtx ctx width) × (scalePrepared (model := model) raw modulus output).Path :=
  let seeded := scaleSeedStep (model := model) (scaleDenominatorCell ctx width) store
  let scaled := scaleStep (model := model) (underScale raw width) (underScale modulus width)
    (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
    (scaleDivisionCell ctx width) (writeUnderScale output width) seeded.1
  (scaled.1, (seeded.2, scaled.2))

/-- Complete scale circuit with all three actual allocations and their matching releases. -/
def withScale (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (scaleDenominatorCtx ctx width) (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
      (.workspace (scaleProductCtx ctx width) (scaleProductCtx ctx width).canonicalFreshKey
        (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh
        (scalePrepared (model := model) raw modulus output)))

/-- The actual complete outer store and complete native finite path. -/
def withScaleStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (withScale (model := model) raw modulus output).Path :=
  let result := scalePreparedStep (model := model) raw modulus output (enterScale store width)
  (leaveScale result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
