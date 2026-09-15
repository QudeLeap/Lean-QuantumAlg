/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Semantics
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Complete actual scalar-multiplication records and caller frame

Every record below composes the existing interpreter-certified complete
addition, actual stored-bit branch and chronological finite sequence. The
result retains every full quantum-reference matrix block and actual history.
The freshly retained entry preserves every original structural classical
read. These execution and frame statements do not assume point validity or
assert the later mathematical scalar-multiple theorem.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- Record the real complete-addition arm, or the actual identity arm for a clear bit. -/
def scalarBitArmStep (spec : CurveSpec width) (point : CInputRef ctx (PointShape width))
    (accumulator : CWriteRef ctx (PointShape width)) (value : CShape.Value .bit) :
    Store ctx → Store ctx × (scalarBitArm spec point accumulator value).Path :=
  match value with
  | .bit true => Add.Native.addIntoStep spec
      (Add.Native.classifierRead accumulator) point accumulator
  | .bit false => fun store => (store, ())

/-- The stored value selects the actual addition result or the unchanged incoming store. -/
theorem scalarBitArmStep_store (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (store : Store ctx) :
    (scalarBitArmStep spec point accumulator value store).1 =
      if value.toBool then
        (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
          point accumulator store).1
      else store := by
  cases value with
  | bit flag => cases flag <;> rfl

private theorem scalarBitArm_execute (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scalarBitArm spec point accumulator value).execute Reference state =
      state.mapClassical (fun entry =>
        ((scalarBitArmStep spec point accumulator value entry.1).1,
          (entry.2, (scalarBitArmStep spec point accumulator value entry.1).2))) := by
  cases value with
  | bit flag =>
      cases flag
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · exact Add.Native.addInto_execute spec _ point accumulator Reference state

/-- The real selector records the bit read from its incoming store and its chosen arm. -/
def scalarSelectedStep (spec : CurveSpec width) (bit : CInputRef ctx .bit)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx) :
    Store ctx × (Circuit.branch bit (scalarBitArm spec point accumulator)).Path :=
  let value := store.read bit
  let selected := scalarBitArmStep spec point accumulator value store
  (selected.1, ⟨value, selected.2⟩)

private theorem scalarSelected_execute (spec : CurveSpec width) (bit : CInputRef ctx .bit)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.branch bit (scalarBitArm spec point accumulator)).execute Reference state =
      state.mapClassical (fun entry =>
        ((scalarSelectedStep spec bit point accumulator entry.1).1,
          (entry.2, (scalarSelectedStep spec bit point accumulator entry.1).2))) :=
  Circuit.execute_branch_mapClassical bit (scalarBitArm spec point accumulator)
    (scalarBitArmStep spec point accumulator)
    (fun value reference {_} _ initial =>
      scalarBitArm_execute spec point accumulator value reference initial) Reference state

/-- Doubling returns the actual store on which the same slot reads its original bit. -/
def scalarSlotStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) : Store ctx → Store ctx × (scalarSlot spec bits point accumulator
      index).Path :=
  Circuit.sequenceRecord
    (Add.Native.addInto spec (Add.Native.classifierRead accumulator)
      (Add.Native.classifierRead accumulator) accumulator)
    (.branch (.vectorGet bits index) (scalarBitArm spec point accumulator))
    (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
      (Add.Native.classifierRead accumulator) accumulator)
    (scalarSelectedStep spec (.vectorGet bits index) point accumulator)

/-- Each slot tests its original indexed bit on the actual store returned by doubling. -/
theorem scalarSlotStep_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (store : Store ctx) :
    (scalarSlotStep spec bits point accumulator index store).1 =
      let doubled := (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
        (Add.Native.classifierRead accumulator) accumulator store).1
      if (doubled.read (.vectorGet bits index)).toBool then
        (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
          point accumulator doubled).1
      else doubled :=
  scalarBitArmStep_store spec point accumulator _ _

/-- Each literal scalar slot preserves complete quantum-reference blocks and both actual paths. -/
theorem scalarSlot_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scalarSlot spec bits point accumulator index).execute Reference state =
      state.mapClassical (fun entry =>
        ((scalarSlotStep spec bits point accumulator index entry.1).1,
          (entry.2, (scalarSlotStep spec bits point accumulator index entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _
    (fun reference {_} _ initial =>
      Add.Native.addInto_execute spec _ _ accumulator reference initial)
    (fun reference {_} _ initial =>
      scalarSelected_execute spec (.vectorGet bits index) point accumulator reference initial)
    Reference state

/-- The actual scalar fold records every declared slot in increasing finite-index order. -/
def scalarFoldStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (scalarFold spec bits point accumulator).Path :=
  Circuit.forRangeRecord scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator)

/-- The actual final store is the chronological fold of all original scalar-slot updates. -/
theorem scalarFoldStep_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx) :
    (scalarFoldStep spec bits point accumulator store).1 =
      (List.ofFn (fun index => fun current =>
        (scalarSlotStep spec bits point accumulator index current).1)).foldl
          (fun current update => update current) store :=
  Circuit.forRangeRecord_store scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator) store

/-- Complete actual state evolution follows the original chronological scalar-slot fold. -/
theorem scalarFold_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scalarFold spec bits point accumulator).execute Reference state =
      state.mapClassical (fun entry =>
        ((scalarFoldStep spec bits point accumulator entry.1).1,
          (entry.2, (scalarFoldStep spec bits point accumulator entry.1).2))) :=
  Circuit.execute_forRangeRecord scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator)
    (fun index reference {_} _ initial =>
      scalarSlot_execute spec bits point accumulator index reference initial) Reference state

/-- Record actual infinity initialization before the real scalar fold. -/
def scalarStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (scalarInto spec bits point accumulator).Path :=
  Circuit.sequenceRecord (Add.Native.infinityInto accumulator)
    (scalarFold spec bits point accumulator) (Add.Native.infinityStep accumulator)
    (scalarFoldStep spec bits point accumulator)

/-- The initialized scalar fold starts from the actual unique infinity write in every store. -/
theorem scalarStep_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx) :
    (scalarStep spec bits point accumulator store).1 =
      (scalarFoldStep spec bits point accumulator
        (store.write accumulator (.ellipticCurvePoint true 0 0))).1 :=
  congrArg (fun current => (scalarFoldStep spec bits point accumulator current).1)
    (Add.Native.infinityStep_store accumulator store)

/-- An empty declared scalar executes only initialization and stores the unique infinity code. -/
theorem scalarStep_zero_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector 0 .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx) :
    (scalarStep spec bits point accumulator store).1 =
      store.write accumulator (.ellipticCurvePoint true 0 0) :=
  scalarStep_store spec bits point accumulator store

/-- The original complete scalar program has one interpreter-certified record for every store. -/
theorem scalarInto_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scalarInto spec bits point accumulator).execute Reference state =
      state.mapClassical (fun entry =>
        ((scalarStep spec bits point accumulator entry.1).1,
          (entry.2, (scalarStep spec bits point accumulator entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _
    (fun reference {_} _ initial => Add.Native.infinityInto_execute accumulator reference initial)
    (fun reference {_} _ initial =>
      scalarFold_execute spec bits point accumulator reference initial) Reference state

private theorem scalarBitArmStep_preserves_read (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (store : Store ctx) {shape : CShape}
    (observed : CInputRef ctx shape) (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarBitArmStep spec point accumulator value store).1.read observed =
      store.read observed := by
  cases value with
  | bit flag =>
      cases flag
      · rfl
      · exact Add.Native.addInto_preserves_read spec _ point accumulator store observed separate

/-- A real scalar slot changes only its accumulator, even on arbitrary noncanonical inputs. -/
theorem scalarSlotStep_preserves_read (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (store : Store ctx) {shape : CShape}
    (observed : CInputRef ctx shape) (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarSlotStep spec bits point accumulator index store).1.read observed =
      store.read observed :=
  (scalarBitArmStep_preserves_read spec point accumulator _ _ observed separate).trans
    (Add.Native.addInto_preserves_read spec _ _ accumulator store observed separate)

/-- All slots retain each original value outside the one actual accumulator. -/
theorem scalarFoldStep_preserves_read (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarFoldStep spec bits point accumulator store).1.read observed = store.read observed :=
  Circuit.forRangeRecord_invariant scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator)
    (fun _ current => current.read observed = store.read observed)
    (fun index current established =>
      (scalarSlotStep_preserves_read spec bits point accumulator index current
        observed separate).trans established) store rfl

/-- Initialization and all actual scalar slots preserve the caller frame together. -/
theorem scalarStep_preserves_read (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarStep spec bits point accumulator store).1.read observed = store.read observed :=
  (scalarFoldStep_preserves_read spec bits point accumulator _ observed separate).trans
    (Add.Native.infinityInto_preserves_read accumulator store observed separate)

/-- Actual retained allocation precedes the certified initialization and scalar-fold record. -/
def scalarRetainedStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (store : Store ctx) : Store (ctx.addRetained key (PointShape width) fresh) ×
      (scalarRetained spec bits point key fresh).Path :=
  let result := scalarStep spec (bits.underRetained key (PointShape width) fresh)
    (point.underRetained key (PointShape width) fresh)
    (CWriteRef.retainedHead ctx key (PointShape width) fresh)
    (store.pushRetained key (PointShape width) fresh)
  (result.1, ((), result.2))

/-- The retained scalar program preserves every full external-reference block and real history. -/
theorem scalarRetained_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scalarRetained spec bits point key fresh).execute Reference state =
      state.mapClassical (fun entry =>
        ((scalarRetainedStep spec bits point key fresh entry.1).1,
          (entry.2, (scalarRetainedStep spec bits point key fresh entry.1).2))) := by
  refine (Circuit.execute_retain_seq_mapClassical ctx key (PointShape width) fresh
    (scalarInto spec (bits.underRetained key (PointShape width) fresh)
      (point.underRetained key (PointShape width) fresh)
      (CWriteRef.retainedHead ctx key (PointShape width) fresh))
    (scalarStep spec (bits.underRetained key (PointShape width) fresh)
      (point.underRetained key (PointShape width) fresh)
      (CWriteRef.retainedHead ctx key (PointShape width) fresh))
    (fun reference {_} _ initial => scalarInto_execute spec _ _ _ reference initial)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual fresh retention derives preservation of every original caller read without a promise. -/
theorem scalarRetainedStep_read_original (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape) :
    (scalarRetainedStep spec bits point key fresh store).1.read
      (observed.underRetained key (PointShape width) fresh) = store.read observed :=
  (scalarStep_preserves_read spec _ _ _ _ _
    (CInputRef.fresh_not_mem_storageKeys_underRetained observed key (PointShape width) fresh)).trans
      (Store.read_pushRetained_underRetained store key (PointShape width) fresh observed)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
