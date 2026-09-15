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

private theorem checkedPack_read_other (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (checkedPackStep cells output store).1.read other = store.read other :=
  (pack_read_other cells output other free.payload free.output
    (FactorRange.storeStep (checkRefs cells) store)).trans
      (FactorRange.read_other (checkRefs cells) other free.lower free.upper store)

private theorem right_read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (rightStep halfPower cells output store).1.read other = store.read other :=
  (checkedPack_read_other cells output other free
    (NativeHalfGCD.step true halfPower cells.candidate store).1).trans
      (NativeHalfGCD.read_other true halfPower cells.candidate other free.candidate store)

private theorem chooseArm_read_other
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other)
    (value : CShape.Value .bit) (store : Store ctx) :
    (chooseArmStep halfPower cells output value store).1.read other = store.read other := by
  cases value with
  | bit bit =>
    cases bit
    · exact right_read_other halfPower cells output other free store
    · exact pack_read_other cells output other free.payload free.output store

private theorem choose_read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (chooseStep halfPower cells output store).1.read other = store.read other :=
  chooseArm_read_other halfPower cells output other free
    (store.read (.storage cells.lower.toCStorageRef)) store

/-- Either actually selected GCD path preserves every read outside its real write cells. -/
theorem read_other (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (step halfPower cells output store).1.read other = store.read other :=
  (choose_read_other halfPower cells output other free
    (FactorRange.storeStep (checkRefs cells)
      (NativeHalfGCD.step false halfPower cells.candidate store).1)).trans
      ((FactorRange.read_other (checkRefs cells) other free.lower free.upper
        (NativeHalfGCD.step false halfPower cells.candidate store).1).trans
          (NativeHalfGCD.read_other false halfPower cells.candidate other free.candidate store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
