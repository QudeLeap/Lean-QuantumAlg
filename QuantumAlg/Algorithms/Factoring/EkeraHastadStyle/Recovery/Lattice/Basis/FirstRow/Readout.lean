/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.FirstRow
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual values of the original first-basis-row loading

The two native resizes read the original decoded sample words and the last
increment reads the original third coordinate. The positional conditions
are precisely the facts supplied by separate actual fresh basis cells and
original sample references. No initial value is assumed here; allocation
will establish the zero third coordinate when forming the source basis.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.FirstRow

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- The literal three writes preserve every structural read outside their actual destinations. -/
theorem nativeLattice_firstRow_read_other
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (refs : Refs ctx width)
    {shape : CShape} (other : CInputRef ctx shape)
    (firstFree : refs.first.key ∉ other.storageKeys)
    (secondFree : refs.second.key ∉ other.storageKeys)
    (thirdFree : refs.third.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep first second refs store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys
    ((store.applyOp (resizeOp first refs.first)).applyOp (resizeOp second refs.second))
    (oneOp refs) other thirdFree).trans
    ((Store.read_applyOp_of_not_mem_storageKeys
      (store.applyOp (resizeOp first refs.first)) (resizeOp second refs.second)
      other secondFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (resizeOp first refs.first)
        other firstFree))

/-- Separate actual destinations contain the two original resizes and the original increment. -/
theorem nativeLattice_firstRow_read
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (refs : Refs ctx width)
    (firstSecond : refs.first.key ≠ refs.second.key)
    (firstThird : refs.first.key ≠ refs.third.key)
    (secondThird : refs.second.key ≠ refs.third.key)
    (secondSource : refs.first.key ∉ second.storageKeys) (store : Store ctx) :
    ((storeStep first second refs store).read (.storage refs.first.toCStorageRef)).toNat =
        (store.read first).toNat % 2 ^ width ∧
      ((storeStep first second refs store).read (.storage refs.second.toCStorageRef)).toNat =
        (store.read second).toNat % 2 ^ width ∧
      ((storeStep first second refs store).read (.storage refs.third.toCStorageRef)).toNat =
        ((store.read (.storage refs.third.toCStorageRef)).toNat + 1) % 2 ^ width := by
  let afterFirst := store.applyOp (resizeOp first refs.first)
  let afterSecond := afterFirst.applyOp (resizeOp second refs.second)
  have sourceRead : afterFirst.read second = store.read second :=
    Store.read_applyOp_of_not_mem_storageKeys store (resizeOp first refs.first)
      second secondSource
  have firstValue : (afterFirst.read (.storage refs.first.toCStorageRef)).toNat =
      (store.read first).toNat % 2 ^ width :=
    congrArg CShape.Value.toNat (Store.read_applyOp_output store (resizeOp first refs.first))
  have secondValue : (afterSecond.read (.storage refs.second.toCStorageRef)).toNat =
      (store.read second).toNat % 2 ^ width :=
    (congrArg CShape.Value.toNat
      (Store.read_applyOp_output afterFirst (resizeOp second refs.second))).trans
      (congrArg (fun value : CShape.Value (.unsignedWord sourceWidth) =>
        value.toNat % 2 ^ width) sourceRead)
  have firstAfterSecond : afterSecond.read (.storage refs.first.toCStorageRef) =
      afterFirst.read (.storage refs.first.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys afterFirst (resizeOp second refs.second)
      (.storage refs.first.toCStorageRef) (by
        simpa only [CInputRef.storageKeys, List.mem_singleton, resizeOp,
          ClassicalOp.outputRef] using firstSecond.symm)
  have firstAfterThird : (storeStep first second refs store).read
      (.storage refs.first.toCStorageRef) = afterSecond.read (.storage refs.first.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys afterSecond (oneOp refs)
      (.storage refs.first.toCStorageRef) (by
        simpa only [CInputRef.storageKeys, List.mem_singleton, oneOp,
          ClassicalOp.outputRef] using firstThird.symm)
  have secondAfterThird : (storeStep first second refs store).read
      (.storage refs.second.toCStorageRef) =
        afterSecond.read (.storage refs.second.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys afterSecond (oneOp refs)
      (.storage refs.second.toCStorageRef) (by
        simpa only [CInputRef.storageKeys, List.mem_singleton, oneOp,
          ClassicalOp.outputRef] using secondThird.symm)
  have thirdAfterFirst : afterFirst.read (.storage refs.third.toCStorageRef) =
      store.read (.storage refs.third.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys store (resizeOp first refs.first)
      (.storage refs.third.toCStorageRef) (by
        simpa only [CInputRef.storageKeys, List.mem_singleton, resizeOp,
          ClassicalOp.outputRef] using firstThird)
  have thirdAfterSecond : afterSecond.read (.storage refs.third.toCStorageRef) =
      afterFirst.read (.storage refs.third.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys afterFirst (resizeOp second refs.second)
      (.storage refs.third.toCStorageRef) (by
        simpa only [CInputRef.storageKeys, List.mem_singleton, resizeOp,
          ClassicalOp.outputRef] using secondThird)
  have thirdValue : ((storeStep first second refs store).read
      (.storage refs.third.toCStorageRef)).toNat =
        ((afterSecond.read (.storage refs.third.toCStorageRef)).toNat + 1) % 2 ^ width :=
    congrArg CShape.Value.toNat (Store.read_applyOp_output afterSecond (oneOp refs))
  exact ⟨(congrArg CShape.Value.toNat (firstAfterThird.trans firstAfterSecond)).trans firstValue,
    (congrArg CShape.Value.toNat secondAfterThird).trans secondValue,
    thirdValue.trans (congrArg (fun value : CShape.Value (.unsignedWord width) =>
      (value.toNat + 1) % 2 ^ width) (thirdAfterSecond.trans thirdAfterFirst))⟩

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.FirstRow
