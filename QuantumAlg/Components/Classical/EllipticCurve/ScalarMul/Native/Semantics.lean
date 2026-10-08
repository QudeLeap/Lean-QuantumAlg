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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Record the real complete-addition arm, or the actual identity arm for a clear bit. -/
def scalarBitArmStep (spec : CurveSpec width) (point : CInputRef ctx (PointShape width))
    (accumulator : CWriteRef ctx (PointShape width)) (value : CShape.Value .bit) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (scalarBitArm spec point accumulator value).Path :=
  match value with
  | .bit true => Add.Native.addIntoStep spec
      (Add.Native.classifierRead accumulator) point accumulator
  | .bit false => fun entry => (entry, ())

/-- The stored value selects the actual addition result or the unchanged incoming store. -/
theorem scalarBitArmStep_store (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (entry : Store ctx × model.HiddenState) :
    (scalarBitArmStep spec point accumulator value entry).1.1 =
      if value.toBool then
        (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
          point accumulator entry).1.1
      else entry.1 := by
  cases value with
  | bit flag => cases flag <;> rfl

private theorem scalarBitArm_execute (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scalarBitArm spec point accumulator value).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalarBitArmStep spec point accumulator value (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  cases value with
  | bit flag =>
      cases flag
      · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · exact Add.Native.addInto_execute spec _ point accumulator Reference state

/-- The real selector records the bit read from its incoming store and its chosen arm. -/
def scalarSelectedStep (spec : CurveSpec width) (bit : CInputRef ctx .bit)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (entry : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) ×
      (Circuit.branch bit (scalarBitArm spec point accumulator)).Path :=
  let value := entry.1.read bit
  let selected := scalarBitArmStep spec point accumulator value entry
  (selected.1, ⟨value, selected.2⟩)

private theorem scalarSelected_execute (spec : CurveSpec width) (bit : CInputRef ctx .bit)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.branch bit (scalarBitArm spec point accumulator)).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalarSelectedStep spec bit point accumulator (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_branch_mapClassical bit (scalarBitArm spec point accumulator)
    (scalarBitArmStep spec point accumulator)
    (fun value reference {_} _ initial =>
      scalarBitArm_execute spec point accumulator value reference initial) Reference state

/-- Doubling returns the actual store on which the same slot reads its original bit. -/
def scalarSlotStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (scalarSlot spec bits point accumulator index).Path :=
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
    (index : Fin scalarWidth) (entry : Store ctx × model.HiddenState) :
    (scalarSlotStep spec bits point accumulator index entry).1.1 =
      let doubled := (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
        (Add.Native.classifierRead accumulator) accumulator entry).1
      if (doubled.1.read (.vectorGet bits index)).toBool then
        (Add.Native.addIntoStep spec (Add.Native.classifierRead accumulator)
          point accumulator doubled).1.1
      else doubled.1 :=
  scalarBitArmStep_store spec point accumulator _ _

/-- Each literal scalar slot preserves complete quantum-reference blocks and both actual paths. -/
theorem scalarSlot_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scalarSlot spec bits point accumulator index).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalarSlotStep spec bits point accumulator index (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
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
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (scalarFold spec bits point accumulator).Path :=
  Circuit.forRangeRecord scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator)

/-- The actual final store is the chronological fold of all original scalar-slot updates. -/
theorem scalarFoldStep_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (entry : Store ctx × model.HiddenState) :
    (scalarFoldStep spec bits point accumulator entry).1 =
      (List.ofFn (fun index => fun current =>
        (scalarSlotStep spec bits point accumulator index current).1)).foldl
          (fun current update => update current) entry :=
  Circuit.forRangeRecord_state scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator) entry

/-- Complete actual state evolution follows the original chronological scalar-slot fold. -/
theorem scalarFold_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scalarFold spec bits point accumulator).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalarFoldStep spec bits point accumulator (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator)
    (fun index reference {_} _ initial =>
      scalarSlot_execute spec bits point accumulator index reference initial) Reference state

/-- Record actual infinity initialization before the real scalar fold. -/
def scalarStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width)) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × (scalarInto spec bits point accumulator).Path :=
  Circuit.sequenceRecord (Add.Native.infinityInto accumulator)
    (scalarFold spec bits point accumulator)
    (Circuit.preserveHiddenRecord (Add.Native.infinityStep accumulator))
    (scalarFoldStep spec bits point accumulator)

/-- The initialized scalar fold starts from the actual unique infinity write in every store. -/
theorem scalarStep_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (entry : Store ctx × model.HiddenState) :
    (scalarStep spec bits point accumulator entry).1 =
      (scalarFoldStep spec bits point accumulator
        (entry.1.write accumulator (.ellipticCurvePoint true 0 0), entry.2)).1 := by
  change (scalarFoldStep spec bits point accumulator
    (Circuit.preserveHiddenRecord (Add.Native.infinityStep accumulator) entry).1).1 = _
  rw [show (Circuit.preserveHiddenRecord (Add.Native.infinityStep accumulator) entry).1 =
    (entry.1.write accumulator (.ellipticCurvePoint true 0 0), entry.2) by
      exact Prod.ext (Add.Native.infinityStep_store accumulator entry.1) rfl]

/-- An empty declared scalar executes only initialization and stores the unique infinity code. -/
theorem scalarStep_zero_store (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector 0 .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (entry : Store ctx × model.HiddenState) :
    (scalarStep spec bits point accumulator entry).1.1 =
      entry.1.write accumulator (.ellipticCurvePoint true 0 0) := by
  rw [scalarStep_store]
  rfl

/-- The original complete scalar program has one interpreter-certified record for every store. -/
theorem scalarInto_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scalarInto spec bits point accumulator).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalarStep spec bits point accumulator (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_sequenceRecord _ _ _ _
    (fun reference {_} _ initial => by
      refine (Add.Native.infinityInto_execute accumulator reference initial).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl)
    (fun reference {_} _ initial =>
      scalarFold_execute spec bits point accumulator reference initial) Reference state

private theorem scalarBitArmStep_preserves_read (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (entry : Store ctx × model.HiddenState) {shape : CShape}
    (observed : CInputRef ctx shape) (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarBitArmStep spec point accumulator value entry).1.1.read observed =
      entry.1.read observed := by
  cases value with
  | bit flag =>
      cases flag
      · rfl
      · exact Add.Native.addInto_preserves_read spec _ point accumulator
          entry.1 entry.2 observed separate

/-- A real scalar slot changes only its accumulator, even on arbitrary noncanonical inputs. -/
theorem scalarSlotStep_preserves_read (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (entry : Store ctx × model.HiddenState) {shape : CShape}
    (observed : CInputRef ctx shape) (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarSlotStep spec bits point accumulator index entry).1.1.read observed =
      entry.1.read observed :=
  (scalarBitArmStep_preserves_read spec point accumulator _ _ observed separate).trans
    (Add.Native.addInto_preserves_read spec _ _ accumulator entry.1 entry.2 observed separate)

/-- All slots retain each original value outside the one actual accumulator. -/
theorem scalarFoldStep_preserves_read (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (entry : Store ctx × model.HiddenState) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarFoldStep spec bits point accumulator entry).1.1.read observed =
      entry.1.read observed :=
  Circuit.forRangeRecord_invariant scalarWidth (scalarSlot spec bits point accumulator)
    (scalarSlotStep spec bits point accumulator)
    (fun _ current => current.1.read observed = entry.1.read observed)
    (fun index current established =>
      (scalarSlotStep_preserves_read spec bits point accumulator index current
        observed separate).trans established) entry rfl

/-- Initialization and all actual scalar slots preserve the caller frame together. -/
theorem scalarStep_preserves_read (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (entry : Store ctx × model.HiddenState) {shape : CShape}
    (observed : CInputRef ctx shape)
    (separate : accumulator.key ∉ observed.storageKeys) :
    (scalarStep spec bits point accumulator entry).1.1.read observed =
      entry.1.read observed :=
  (scalarFoldStep_preserves_read spec bits point accumulator _ observed separate).trans
    (Add.Native.infinityInto_preserves_read accumulator entry.1 observed separate)

/-- Actual retained allocation precedes the certified initialization and scalar-fold record. -/
def scalarRetainedStep (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (entry : Store ctx × model.HiddenState) :
    (Store (ctx.addRetained key (PointShape width) fresh) × model.HiddenState) ×
      (scalarRetained spec bits point key fresh).Path :=
  let result := scalarStep spec (bits.underRetained key (PointShape width) fresh)
    (point.underRetained key (PointShape width) fresh)
    (CWriteRef.retainedHead ctx key (PointShape width) fresh)
    (entry.1.pushRetained key (PointShape width) fresh, entry.2)
  (result.1, ((), result.2))

/-- The retained scalar program preserves every full external-reference block and real history. -/
theorem scalarRetained_execute (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scalarRetained spec bits point key fresh).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scalarRetainedStep spec bits point key fresh (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_retain_seq_mapClassical ctx key (PointShape width) fresh
    (scalarInto spec (bits.underRetained key (PointShape width) fresh)
      (point.underRetained key (PointShape width) fresh)
      (CWriteRef.retainedHead ctx key (PointShape width) fresh))
    (scalarStep spec (bits.underRetained key (PointShape width) fresh)
      (point.underRetained key (PointShape width) fresh)
      (CWriteRef.retainedHead ctx key (PointShape width) fresh))
    (fun reference {_} _ initial => scalarInto_execute spec _ _ _ reference initial)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual fresh retention derives preservation of every original caller read without a promise. -/
theorem scalarRetainedStep_read_original (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (entry : Store ctx × model.HiddenState) {shape : CShape}
    (observed : CInputRef ctx shape) :
    (scalarRetainedStep spec bits point key fresh entry).1.1.read
      (observed.underRetained key (PointShape width) fresh) = entry.1.read observed :=
  (scalarStep_preserves_read spec _ _ _ _ _
    (CInputRef.fresh_not_mem_storageKeys_underRetained observed key (PointShape width) fresh)).trans
      (Store.read_pushRetained_underRetained entry.1 key (PointShape width) fresh observed)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
