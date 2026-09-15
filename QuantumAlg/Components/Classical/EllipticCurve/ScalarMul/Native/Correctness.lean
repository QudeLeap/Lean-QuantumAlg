/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Correctness
import all QuantumAlg.Util.Classical.EllipticCurve.ScalarMul

/-!
# Original natural scalar action from the actual retained program

The actual indexed stores follow the original most-significant-first accumulated
scalar evaluator. Complete addition supplies each real point transition.
Fresh retained allocation derives separation of the original scalar bits and
base point from the accumulator. Only their original same-store mathematical
representations are hypotheses of the retained result theorem.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

private theorem scalarSlotStep_represents_msbStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (store : Store ctx) (base accumulated : Pure.Point spec) (bit : Bool)
    (bitsFree : accumulator.key ∉ bits.storageKeys)
    (pointFree : accumulator.key ∉ point.storageKeys)
    (baseRep : PointRepresents spec (store.read point) base)
    (partialRep : PointRepresents spec (store.read (Add.Native.classifierRead accumulator))
      accumulated)
    (bitValue : (store.read (.vectorGet bits index)).toBool = bit) :
    PointRepresents spec
      ((scalarSlotStep spec bits point accumulator index store).1.read
        (Add.Native.classifierRead accumulator))
      (ClassicalAlgorithms.EllipticCurve.ScalarMul.msbStep spec base accumulated bit) := by
  let doubled := (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
    (Add.Native.classifierRead accumulator) accumulator store).1
  have doubledRep : PointRepresents spec (doubled.read (Add.Native.classifierRead accumulator))
      (ClassicalAlgorithms.EllipticCurve.Double.eval spec accumulated) :=
    Add.Native.addIntoStep_represents spec _ _ accumulator store accumulated accumulated partialRep
      partialRep
  have pointRead : doubled.read point = store.read point :=
    Add.Native.addInto_preserves_read spec _ _ accumulator store point pointFree
  have doubledBase : PointRepresents spec (doubled.read point) base := by
    rw [pointRead]
    exact baseRep
  have selectedRead : doubled.read (.vectorGet bits index) =
      store.read (.vectorGet bits index) :=
    Add.Native.addInto_preserves_read spec _ _ accumulator store (.vectorGet bits index) bitsFree
  have selectedBit : (doubled.read (.vectorGet bits index)).toBool = bit :=
    (congrArg (fun value : CShape.Value .bit => value.toBool) selectedRead).trans bitValue
  rw [scalarSlotStep_store]
  change PointRepresents spec
    ((if (doubled.read (.vectorGet bits index)).toBool then
      (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
        point accumulator doubled).1 else doubled).read (Add.Native.classifierRead accumulator)) _
  rw [selectedBit]
  cases bit with
  | false => exact doubledRep
  | true =>
      exact Add.Native.addIntoStep_represents spec _ point accumulator doubled _ base
        doubledRep doubledBase

/-- The actual caller accumulator represents the original natural scalar under input separation. -/
theorem scalarStep_represents_eval (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx)
    (input : ClassicalAlgorithms.EllipticCurve.ScalarMul.Input spec scalarWidth)
    (bitsFree : accumulator.key ∉ bits.storageKeys)
    (pointFree : accumulator.key ∉ point.storageKeys)
    (scalarRep : ∀ index, (store.read (.vectorGet bits index)).toBool =
      ClassicalAlgorithms.EllipticCurve.ScalarMul.scalarBit input.scalar index)
    (pointRep : PointRepresents spec (store.read point) input.point) :
    PointRepresents spec
      ((scalarStep spec bits point accumulator store).1.read
        (Add.Native.classifierRead accumulator))
      (input.scalar.val • input.point) := by
  let Invariant (processed : Nat) (current : Store ctx) : Prop :=
    current.read bits = store.read bits ∧ current.read point = store.read point ∧
      PointRepresents spec (current.read (Add.Native.classifierRead accumulator))
        (ClassicalAlgorithms.EllipticCurve.ScalarMul.partialEval spec input processed)
  have advance : ∀ (index : Fin scalarWidth) current, Invariant index.val current →
      Invariant (index.val + 1) (scalarSlotStep spec bits point accumulator index current).1 := by
    intro index current established
    refine ⟨(scalarSlotStep_preserves_read spec bits point accumulator index current
      bits bitsFree).trans established.1,
      (scalarSlotStep_preserves_read spec bits point accumulator index current
        point pointFree).trans established.2.1, ?_⟩
    have currentPoint : PointRepresents spec (current.read point) input.point := by
      rw [established.2.1]
      exact pointRep
    have currentBit : (current.read (.vectorGet bits index)).toBool =
        ClassicalAlgorithms.EllipticCurve.ScalarMul.scalarBit input.scalar index := by
      change ((current.read bits).get index).toBool = _
      rw [established.1]
      exact scalarRep index
    have pointStep := scalarSlotStep_represents_msbStep spec bits point accumulator index current
      input.point _ _ bitsFree pointFree currentPoint established.2.2 currentBit
    rw [ClassicalAlgorithms.EllipticCurve.ScalarMul.msbStep_partialEval] at pointStep
    exact pointStep
  let initialized := (Add.Native.infinityStep accumulator store).1
  have initial : Invariant 0 initialized := by
    refine ⟨Add.Native.infinityInto_preserves_read accumulator store bits bitsFree,
      Add.Native.infinityInto_preserves_read accumulator store point pointFree, ?_⟩
    rw [ClassicalAlgorithms.EllipticCurve.ScalarMul.partialEval_zero]
    exact Add.Native.infinityInto_represents spec accumulator store
  have completed := Circuit.forRangeRecord_invariant scalarWidth
    (scalarSlot spec bits point accumulator) (scalarSlotStep spec bits point accumulator)
    Invariant advance initialized initial
  have finalPoint := completed.2.2
  rw [ClassicalAlgorithms.EllipticCurve.ScalarMul.partialEval_final] at finalPoint
  exact finalPoint

/-- The real retained output is the original natural scalar multiple, including width zero. -/
theorem scalarRetainedStep_represents (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (store : Store ctx)
    (input : ClassicalAlgorithms.EllipticCurve.ScalarMul.Input spec scalarWidth)
    (scalarRep : ∀ index, (store.read (.vectorGet bits index)).toBool =
      ClassicalAlgorithms.EllipticCurve.ScalarMul.scalarBit input.scalar index)
    (pointRep : PointRepresents spec (store.read point) input.point) :
    PointRepresents spec
      ((scalarRetainedStep spec bits point key fresh store).1.read
        (.storage (CStorageRef.retainedHead ctx key (PointShape width) fresh)))
      (input.scalar.val • input.point) := by
  apply scalarStep_represents_eval spec
    (bits.underRetained key (PointShape width) fresh)
    (point.underRetained key (PointShape width) fresh)
    (CWriteRef.retainedHead ctx key (PointShape width) fresh)
    (store.pushRetained key (PointShape width) fresh) input
  · exact CInputRef.fresh_not_mem_storageKeys_underRetained bits key (PointShape width) fresh
  · exact CInputRef.fresh_not_mem_storageKeys_underRetained point key (PointShape width) fresh
  · intro index
    change (((store.pushRetained key (PointShape width) fresh).read
      (bits.underRetained key (PointShape width) fresh)).get index).toBool = _
    rw [Store.read_pushRetained_underRetained]
    exact scalarRep index
  · rw [Store.read_pushRetained_underRetained]
    exact pointRep

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
