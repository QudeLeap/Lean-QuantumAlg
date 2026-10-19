/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering.Execution

/-!
# Actual centered-target comparison values

The original scratch is explicitly cleared before equality reads it. Actual
copying and halving preserve the original source and modulus. Both stored
comparison results and the final half-modulus word therefore describe the
original incoming store without an initial-scratch premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual store immediately after native scratch initialization and the zero comparison. -/
def zeroTestStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (store.applyOp (Word.PowerOfTwo.clearOp refs.scratch)).applyOp (zeroOp refs)

/-- Actual store immediately after copying the original modulus into scratch. -/
def modulusStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (zeroTestStore refs store).applyOp (copyOp refs)

/-- Actual store immediately after halving the copied original modulus. -/
def halfStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  (modulusStore refs store).applyOp (Word.Split.shiftOp refs.scratch)

/-- The actual native equality bit compares the actual values read by that instruction. -/
lemma zero_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (zeroOp refs)).read (writeInput refs.isZero)).toBool =
      decide ((store.read refs.a).toNat = (store.read (writeInput refs.scratch)).toNat) := by
  simp only [Store.applyOp, zeroOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordBinary]
  rfl

/-- Actual native copying retains the complete modulus word it reads. -/
lemma copy_read (refs : Refs ctx width) (store : Store ctx) :
    (store.applyOp (copyOp refs)).read (writeInput refs.scratch) = store.read refs.modulus := by
  simp only [Store.applyOp, copyOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordUnary]
  cases store.read refs.modulus
  rfl

/-- The actual native less-than bit compares the actual source and scratch values it reads. -/
lemma below_read (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (belowOp refs)).read (writeInput refs.belowHalf)).toBool =
      decide ((store.read refs.a).toNat < (store.read (writeInput refs.scratch)).toNat) := by
  simp only [Store.applyOp, belowOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordBinary]
  rfl

/-- Clearing and actual zero comparison retain every read outside scratch and the zero flag. -/
lemma zeroTest_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (scratch : refs.scratch.key ∉ other.storageKeys)
    (zero : refs.isZero.key ∉ other.storageKeys) :
    (zeroTestStore refs store).read other = store.read other := by
  unfold zeroTestStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (zeroOp refs) other zero,
    Store.read_applyOp_of_not_mem_storageKeys _ (Word.PowerOfTwo.clearOp refs.scratch)
      other scratch]

/-- Actual clearing, zero testing, copying and halving retain the complete outside frame. -/
lemma halfStore_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (scratch : refs.scratch.key ∉ other.storageKeys)
    (zero : refs.isZero.key ∉ other.storageKeys) :
    (halfStore refs store).read other = store.read other := by
  unfold halfStore modulusStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (Word.Split.shiftOp refs.scratch) other scratch,
    Store.read_applyOp_of_not_mem_storageKeys _ (copyOp refs) other scratch,
    zeroTest_callerFrame refs store other scratch zero]

/-- The actual zero comparison reads the original source and an explicitly cleared scratch word. -/
lemma zeroTest_isZero (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx) :
    ((zeroTestStore refs store).read (writeInput refs.isZero)).toBool =
      decide ((store.read refs.a).toNat = 0) := by
  change (((store.applyOp (Word.PowerOfTwo.clearOp refs.scratch)).applyOp (zeroOp refs)).read
    (writeInput refs.isZero)).toBool = _
  rw [zero_read, Word.PowerOfTwo.clear_read,
    Store.read_applyOp_of_not_mem_storageKeys _ (Word.PowerOfTwo.clearOp refs.scratch)
      refs.a separation.aAvoidsScratch]

/-- Actual halving produces precisely half of the original incoming modulus. -/
lemma halfStore_scratch (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    ((halfStore refs store).read (writeInput refs.scratch)).toNat =
      (store.read refs.modulus).toNat / 2 := by
  change (((modulusStore refs store).applyOp (Word.Split.shiftOp refs.scratch)).read
    (writeInput refs.scratch)).toNat = _
  rw [Word.Split.shift_read]
  change (((zeroTestStore refs store).applyOp (copyOp refs)).read
    (writeInput refs.scratch)).toNat / 2 = _
  rw [copy_read, zeroTest_callerFrame refs store refs.modulus
    separation.modulusAvoidsScratch separation.modulusAvoidsIsZero]

/-- The actual prepared scratch retains the original half modulus through the final comparison. -/
lemma prepare_scratch (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx) :
    ((prepareStore refs store).read (writeInput refs.scratch)).toNat =
      (store.read refs.modulus).toNat / 2 := by
  change (((halfStore refs store).applyOp (belowOp refs)).read (writeInput refs.scratch)).toNat = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (belowOp refs) _
      separation.scratchAvoidsBelowHalf,
    halfStore_scratch refs separation store]

/-- Actual preparation retains the original zero test through copying, halving and comparison. -/
lemma prepare_isZero (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx) :
    ((prepareStore refs store).read (writeInput refs.isZero)).toBool =
      decide ((store.read refs.a).toNat = 0) := by
  change (((halfStore refs store).applyOp (belowOp refs)).read (writeInput refs.isZero)).toBool = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (belowOp refs) _ separation.isZeroAvoidsBelowHalf]
  unfold halfStore modulusStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (Word.Split.shiftOp refs.scratch) _
      separation.isZeroAvoidsScratch,
    Store.read_applyOp_of_not_mem_storageKeys _ (copyOp refs) _ separation.isZeroAvoidsScratch,
    zeroTest_isZero refs separation store]

/-- Actual preparation stores the exact original source-versus-half-modulus comparison. -/
lemma prepare_belowHalf (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    ((prepareStore refs store).read (writeInput refs.belowHalf)).toBool =
      decide ((store.read refs.a).toNat < (store.read refs.modulus).toNat / 2) := by
  change (((halfStore refs store).applyOp (belowOp refs)).read
    (writeInput refs.belowHalf)).toBool = _
  rw [below_read, halfStore_scratch refs separation store,
    halfStore_callerFrame refs store refs.a separation.aAvoidsScratch separation.aAvoidsIsZero]

/-- Actual comparison preparation retains every read outside its three original write identities. -/
lemma prepare_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (scratch : refs.scratch.key ∉ other.storageKeys)
    (zero : refs.isZero.key ∉ other.storageKeys) (below : refs.belowHalf.key ∉ other.storageKeys) :
    (prepareStore refs store).read other = store.read other := by
  change ((halfStore refs store).applyOp (belowOp refs)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (belowOp refs) other below,
    halfStore_callerFrame refs store other scratch zero]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
