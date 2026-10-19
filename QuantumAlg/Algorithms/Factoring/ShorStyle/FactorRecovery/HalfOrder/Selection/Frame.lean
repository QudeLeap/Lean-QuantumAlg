/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Packing
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Preservation
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange

/-!
# Actual structural frame preservation through the priority GCD branches

Both real branch records preserve reads outside their concrete candidate,
comparison, payload and output writes. The scoped consumer discharges these
conditions from its real fresh keys, including retained and workspace inputs.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open Execution ClassicalRoutines.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}

/-- The actual writes of this factor selection are outside the given structural operand. -/
structure FrameFree (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) : Prop where
  candidate : cells.candidate.key ∉ other.storageKeys
  lower : cells.lower.key ∉ other.storageKeys
  upper : cells.upper.key ∉ other.storageKeys
  payload : cells.payload.key ∉ other.storageKeys
  output : output.key ∉ other.storageKeys

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private lemma checkedPack_read_other (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (checkedPackStep (model := model) cells output store).1.read other = store.read other :=
  (pack_read_other (model := model) cells output other free.payload free.output
    (FactorRange.storeStep (checkRefs cells) store)).trans
      (FactorRange.read_other (checkRefs cells) other free.lower free.upper store)

private lemma right_read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (rightStep (model := model) halfPower cells output store).1.read other = store.read other :=
  (checkedPack_read_other (model := model) cells output other free
    (NativeHalfGCD.step (model := model) true halfPower cells.candidate store).1).trans
      (NativeHalfGCD.read_other (model := model) true halfPower cells.candidate other
          free.candidate store)

private lemma chooseArm_read_other
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other)
    (value : CShape.Value .bit) (store : Store ctx) :
    (chooseArmStep (model := model) halfPower cells output value store).1.read other = store.read
        other := by
  cases value with
  | bit bit =>
    cases bit
    · exact right_read_other (model := model) halfPower cells output other free store
    · exact pack_read_other (model := model) cells output other free.payload free.output store

private lemma choose_read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (chooseStep (model := model) halfPower cells output store).1.read other = store.read other :=
  chooseArm_read_other (model := model) halfPower cells output other free
    (store.read (.storage cells.lower.toCStorageRef)) store

/-- Either actually selected GCD path preserves every read outside its real write cells. -/
lemma read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (step (model := model) halfPower cells output store).1.read other = store.read other :=
  (choose_read_other (model := model) halfPower cells output other free
    (FactorRange.storeStep (checkRefs cells)
      (NativeHalfGCD.step (model := model) false halfPower cells.candidate store).1)).trans
      ((FactorRange.read_other (checkRefs cells) other free.lower free.upper
        (NativeHalfGCD.step (model := model) false halfPower cells.candidate store).1).trans
          (NativeHalfGCD.read_other (model := model) false halfPower cells.candidate other
              free.candidate store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
