/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Layout

/-!
# Actual coordinate exchange through one scratch word

Three native copies exchange two actual words and leave the original left
word in the supplied scratch. Every unrelated caller read is preserved.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap

open LatticeArithmetic (writeInput)
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual three-copy exchange of two words through caller-owned scratch. -/
def coordinateSwap (left right scratch : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (LatticeRows.copyOp left scratch))
    (.seq (.classical (LatticeRows.copyOp right left))
      (.classical (LatticeRows.copyOp scratch right)))

/-- The actual chronological writes of one coordinate exchange. -/
def coordinateSwapStore (left right scratch : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  ((store.applyOp (LatticeRows.copyOp left scratch)).applyOp
    (LatticeRows.copyOp right left)).applyOp (LatticeRows.copyOp scratch right)

/-- Reads outside the two exchanged words and scratch survive the actual exchange. -/
theorem coordinateSwap_callerFrame (left right scratch : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoidLeft : left.key ∉ other.storageKeys) (avoidRight : right.key ∉ other.storageKeys)
    (avoidScratch : scratch.key ∉ other.storageKeys) :
    (coordinateSwapStore left right scratch store).read other = store.read other := by
  unfold coordinateSwapStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp scratch right) _ avoidRight,
    Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp right left) _ avoidLeft,
    Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp left scratch) _ avoidScratch]

/-- The actual outputs exchange both original words, with no initial scratch condition. -/
theorem coordinateSwap_reads (left right scratch : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (leftRight : left.key ≠ right.key)
    (leftScratch : left.key ≠ scratch.key) (rightScratch : right.key ≠ scratch.key) :
    (coordinateSwapStore left right scratch store).read (writeInput left) =
        store.read (writeInput right) ∧
      (coordinateSwapStore left right scratch store).read (writeInput right) =
        store.read (writeInput left) := by
  have avoidLeft : right.key ∉ (writeInput left).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using leftRight.symm
  have avoidScratch : left.key ∉ (writeInput scratch).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using leftScratch
  have avoidRight : scratch.key ∉ (writeInput right).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using rightScratch.symm
  unfold coordinateSwapStore
  constructor
  · rw [Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp scratch right) _ avoidLeft,
      LatticeRows.copy_read,
      Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp left scratch) _ avoidRight]
  · rw [LatticeRows.copy_read,
      Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp right left) _ avoidScratch,
      LatticeRows.copy_read]

/-- The actual scratch retains the original left word after the exchange. -/
theorem coordinateSwap_scratch (left right scratch : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) (leftScratch : left.key ≠ scratch.key)
    (rightScratch : right.key ≠ scratch.key) :
    (coordinateSwapStore left right scratch store).read (writeInput scratch) =
      store.read (writeInput left) := by
  have avoidLeft : left.key ∉ (writeInput scratch).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using leftScratch
  have avoidRight : right.key ∉ (writeInput scratch).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using rightScratch
  unfold coordinateSwapStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp scratch right) _ avoidRight,
    Store.read_applyOp_of_not_mem_storageKeys _ (LatticeRows.copyOp right left) _ avoidLeft,
    LatticeRows.copy_read]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap
