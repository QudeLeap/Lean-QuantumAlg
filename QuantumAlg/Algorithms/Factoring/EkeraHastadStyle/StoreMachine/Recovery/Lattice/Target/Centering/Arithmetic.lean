/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering.Readout

/-!
# Actual centered-target selected arithmetic and its frame

Native raw subtraction and complement/increment represent the corresponding
original integer expressions modulo the supplied word width. Every selected
arm writes only the original output and preserves the complete caller frame.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- An actual raw word represents its own original unsigned value modulo the supplied width. -/
theorem rawRepresents_toNat (word : CShape.Word width) :
    RawSignedRepresents word (word.toNat : Int) := Int.ModEq.refl _

/-- The actual native subtraction represents the exact original integer difference modulo width. -/
theorem sub_represents (refs : Refs ctx width) (left right : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) :
    RawSignedRepresents ((store.applyOp (subOp refs left right)).read (writeInput refs.output))
      ((store.read left).toNat - (store.read right).toNat : Int) := by
  simp only [Store.applyOp, subOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordBinary]
  exact rawSignedWordRepresents_sub (store.read left) (store.read right) _ _
    (rawRepresents_toNat _) (rawRepresents_toNat _)

/-- Actual native complement/increment represents the negative of the original source word. -/
theorem negate_represents (refs : Refs ctx width) (store : Store ctx) :
    RawSignedRepresents ((negateStep refs store).1.read (writeInput refs.output))
      (-(store.read refs.a).toNat : Int) := by
  simp only [negateStep, Store.applyOp, complementOp, Word.PowerOfTwo.incrementOp,
    ClassicalOp.outputRef, Store.read_write_same, ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  exact rawSignedWordRepresents_negate (store.read refs.a) _ (rawRepresents_toNat _)

/-- An actual subtraction retains every read outside the original centered output. -/
theorem sub_callerFrame (refs : Refs ctx width) (left right : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.output.key ∉ other.storageKeys) :
    (store.applyOp (subOp refs left right)).read other = store.read other :=
  Store.read_applyOp_of_not_mem_storageKeys store (subOp refs left right) other avoids

/-- Actual complement and increment retain the entire frame outside the original output. -/
theorem negate_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.output.key ∉ other.storageKeys) :
    (negateStep refs store).1.read other = store.read other := by
  change ((store.applyOp (complementOp refs)).applyOp
    (Word.PowerOfTwo.incrementOp refs.output)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (Word.PowerOfTwo.incrementOp refs.output)
      other avoids,
    Store.read_applyOp_of_not_mem_storageKeys _ (complementOp refs) other avoids]

/-- Either selected half-comparison arithmetic arm retains the complete nonoutput caller frame. -/
theorem halfArm_callerFrame (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.output.key ∉ other.storageKeys) :
    (halfArmStep refs flag store).1.read other = store.read other := by
  cases flag with
  | bit flag =>
    cases flag
    · exact sub_callerFrame refs refs.modulus refs.a store other avoids
    · exact negate_callerFrame refs store other avoids

/-- The actual stored half comparison selects an arm that retains the complete caller frame. -/
theorem half_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.output.key ∉ other.storageKeys) :
    (halfStep refs store).1.read other = store.read other :=
  halfArm_callerFrame refs (store.read (writeInput refs.belowHalf)) store other avoids

/-- Either selected zero-test arithmetic arm retains the complete original nonoutput frame. -/
theorem finishArm_callerFrame (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.output.key ∉ other.storageKeys) :
    (finishArmStep refs flag store).1.read other = store.read other := by
  cases flag with
  | bit flag =>
    cases flag
    · exact half_callerFrame refs store other avoids
    · exact sub_callerFrame refs refs.a refs.a store other avoids

/-- The actual stored zero test selects arithmetic that preserves the complete nonoutput frame. -/
theorem finish_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.output.key ∉ other.storageKeys) :
    (finishStep refs store).1.read other = store.read other :=
  finishArm_callerFrame refs (store.read (writeInput refs.isZero)) store other avoids

/-- The complete actual centered loader preserves every read outside its four original writes. -/
theorem centeredTargetInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (scratch : refs.scratch.key ∉ other.storageKeys)
    (zero : refs.isZero.key ∉ other.storageKeys) (below : refs.belowHalf.key ∉ other.storageKeys)
    (output : refs.output.key ∉ other.storageKeys) :
    (centeredTargetStep refs store).1.read other = store.read other := by
  change (finishStep refs (prepareStore refs store)).1.read other = _
  rw [finish_callerFrame refs _ other output,
    prepare_callerFrame refs store other scratch zero below]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
