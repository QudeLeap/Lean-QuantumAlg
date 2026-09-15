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

/-- Original denominator loading: one increment and exactly the raw width's shifts. -/
def scaleSeed (denominator : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .seq (.classical (Word.PowerOfTwo.incrementOp denominator))
    (Word.PowerOfTwo.shiftInto width denominator)

/-- Actual denominator-loading store and its full native path. -/
def scaleSeedStep (denominator : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx) :
    Store ctx × (scaleSeed denominator).Path :=
  (Word.PowerOfTwo.shiftStore width denominator
    (store.applyOp (Word.PowerOfTwo.incrementOp denominator)), ((), fun _ => ()))

/-- The real denominator-loader execution retains every complete quantum-reference block. -/
theorem scaleSeed_execute (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scaleSeed denominator).execute Reference state = state.mapClassical (fun entry =>
      ((scaleSeedStep denominator entry.1).1,
        (entry.2, (scaleSeedStep denominator entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (Word.PowerOfTwo.incrementOp denominator))
    (Word.PowerOfTwo.shiftInto width denominator)
    (fun store => (store.applyOp (Word.PowerOfTwo.incrementOp denominator), ()))
    (Word.PowerOfTwo.shiftStep width denominator) (by
      intro reference history _ initial
      refine (Circuit.execute_classical_mapClassical (Word.PowerOfTwo.incrementOp denominator)
        reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (Word.PowerOfTwo.shiftInto_execute width denominator)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Scope initialization supplies this local zero premise; no old caller cell is constrained. -/
theorem scaleSeed_zero_value (denominator : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) (initial : (store.read (scaleRead denominator)).toNat = 0) :
    ((scaleSeedStep denominator store).1.read (scaleRead denominator)).toNat = 2 ^ width := by
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
    (scaleSeedStep denominator store).1.read other = store.read other :=
  (Word.PowerOfTwo.shiftInto_callerFrame width denominator _ other separate).trans
    (Store.read_applyOp_of_not_mem_storageKeys store
      (Word.PowerOfTwo.incrementOp denominator) other separate)

/-- Actual three arithmetic instructions placed on these exact scratch and caller cells. -/
def scalePlaced (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (scaleCtx ctx width) (scaleCtx ctx width) :=
  scaleBody (underScale raw width) (underScale modulus width)
    (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
    (scaleDivisionCell ctx width) (writeUnderScale output width)

/-- The actual denominator is loaded before the first full-width arithmetic instruction. -/
def scalePrepared (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit (scaleCtx ctx width) (scaleCtx ctx width) :=
  .seq (scaleSeed (scaleDenominatorCell ctx width)) (scalePlaced raw modulus output)

/-- Complete inner store and original chronological loader-and-arithmetic path. -/
def scalePreparedStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (scaleCtx ctx width)) :
    Store (scaleCtx ctx width) × (scalePrepared raw modulus output).Path :=
  let seeded := scaleSeedStep (scaleDenominatorCell ctx width) store
  (scaleStore (underScale raw width) (underScale modulus width)
    (scaleRead (scaleDenominatorCell ctx width)) (scaleProductCell ctx width)
    (scaleDivisionCell ctx width) (writeUnderScale output width) seeded.1,
    (seeded.2, ((), ((), ()))))

/-- Complete scale circuit with all three actual allocations and their matching releases. -/
def withScale (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + 1)) ctx.canonicalFreshKey_fresh
    (.workspace (scaleDenominatorCtx ctx width) (scaleDenominatorCtx ctx width).canonicalFreshKey
      (.unsignedWord (width + (width + 1))) (scaleDenominatorCtx ctx width).canonicalFreshKey_fresh
      (.workspace (scaleProductCtx ctx width) (scaleProductCtx ctx width).canonicalFreshKey
        (scaleDivisionShape width) (scaleProductCtx ctx width).canonicalFreshKey_fresh
        (scalePrepared raw modulus output)))

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

/-- The actual complete outer store and complete native finite path. -/
def withScaleStep (raw : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (withScale raw modulus output).Path :=
  let result := scalePreparedStep raw modulus output (enterScale store width)
  (leaveScale result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
