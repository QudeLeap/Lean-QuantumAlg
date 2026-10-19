/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Core.Execution.Retained.Step

/-!
# Original fixed-count recovery with persistent storage reuse

The original seven latches and scalar accumulator cells are retained once.
Every actual sample then runs all six original attempt stages in chronological
order on those same destinations. After the loop, one real optional-result
cell is retained and the original option-pack instruction reads the actual
first-success latches. All original inputs and retained cells remain live.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth count : Nat}

/-- One real sample uses precisely the seven original persistent destinations. -/
def persistentAttempt {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth)
      (persistentCtx ctx width scalarWidth) :=
  attemptInto curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth)

/-- Actual fixed-count attempts keep all original samples and reuse the same seven cells. -/
def repeatedAttempts {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth)
      (persistentCtx ctx width scalarWidth) :=
  Circuit.forRange count fun index => persistentAttempt curve modulus (samples index) base target

/-- Allocate the original persistent cells once, then execute the original chronological loop. -/
def recoveryBatch {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model ctx (persistentCtx ctx width scalarWidth) :=
  .seq (retainPersistent ctx width scalarWidth) (repeatedAttempts curve modulus samples base target)

/-- The final original optional result is retained after the complete persistent recovery loop. -/
@[implicit_reducible] def batchResultCtx (ctx : RuntimeCtx kind)
    (width scalarWidth : Nat) : RuntimeCtx kind :=
  (persistentCtx ctx width scalarWidth).addRetained
    (persistentCtx ctx width scalarWidth).canonicalFreshKey
    (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh

/-- The final classical result leaves the complete quantum carrier unchanged. -/
lemma batchResultCtx_register (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    (batchResultCtx ctx width scalarWidth).register = ctx.register := by
  rfl

/-- The original optional output is the actual final retained storage cell. -/
def batchResultRead (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    CInputRef (batchResultCtx ctx width scalarWidth) (.option (.unsignedWord scalarWidth)) :=
  let inner := persistentCtx ctx width scalarWidth
  .storage (CStorageRef.retainedHead inner inner.canonicalFreshKey
    (.option (.unsignedWord scalarWidth)) inner.canonicalFreshKey_fresh)

/-- The original closed option-pack instruction reads the actual first-success latches. -/
def batchResultOp (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    ClassicalOp (.product .bit (.unsignedWord scalarWidth)) (.option (.unsignedWord scalarWidth))
      (batchResultCtx ctx width scalarWidth) (batchResultCtx ctx width scalarWidth) :=
  let inner := persistentCtx ctx width scalarWidth
  let shape := CShape.option (.unsignedWord scalarWidth)
  let accepted := CInputRef.storage (persistentAccepted ctx width scalarWidth).toCStorageRef
  let selected := CInputRef.storage (persistentSelected ctx width scalarWidth).toCStorageRef
  .packOption _
    (.product (accepted.underRetained inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh)
      (selected.underRetained inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh))
    (CWriteRef.retainedHead inner inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh)

/-- Actual result retention precedes the original final option-pack instruction. -/
def packBatchResult {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat) :
    Circuit model (persistentCtx ctx width scalarWidth)
      (batchResultCtx ctx width scalarWidth) :=
  let inner := persistentCtx ctx width scalarWidth
  .seq (.retain inner inner.canonicalFreshKey (.option (.unsignedWord scalarWidth))
      inner.canonicalFreshKey_fresh)
    (BitWord.instruction (execution := model) (batchResultOp ctx width scalarWidth))

/-- The complete original fixed-count tail includes the actual final output packing. -/
def recoveryTail {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) : Circuit model ctx
      (batchResultCtx ctx width scalarWidth) :=
  .seq (recoveryBatch curve modulus samples base target) (packBatchResult ctx width scalarWidth)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
