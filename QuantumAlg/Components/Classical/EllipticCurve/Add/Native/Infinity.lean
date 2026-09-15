/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Repack
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Actual initialization of the unique point at infinity

The original bit-not and nominal-packing instructions use internally allocated
false, tag and zero cells. Their complete state theorem retains the caller's
quantum reference, history and all classical values except the destination.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original false source, computed tag and shared zero-coordinate word. -/
def infinityShapes (width : Nat) : List CShape := [.bit, .bit, .unsignedWord width]

/-- The original real bit-not instruction materializes the infinity tag. -/
def infinityTagOp (falseBit : CInputRef ctx .bit) (tag : CWriteRef ctx .bit) :
    ClassicalOp .bit .bit ctx ctx := .bit .not ctx falseBit tag

/-- The original raw infinity input uses the same actual zero word for both coordinates. -/
def infinityRaw (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width)) :
    CInputRef ctx (PointEquality.RawPointShape width) :=
  .product (classifierRead tag) (.product zero zero)

/-- The actual original two-instruction infinity initialization body. -/
def infinityBody (falseBit : CInputRef ctx .bit) (tag : CWriteRef ctx .bit)
    (zero : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (PointShape width)) :
    Circuit ctx ctx :=
  .seq (.classical (infinityTagOp falseBit tag)) (repackRawInto (infinityRaw tag zero) output)

/-- The real store after the original tag update and nominal-point packing. -/
def infinityBodyStore (falseBit : CInputRef ctx .bit) (tag : CWriteRef ctx .bit)
    (zero : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) : Store ctx :=
  repackStore (infinityRaw tag zero) output (store.applyOp (infinityTagOp falseBit tag))

/-- Both actual native instructions preserve all complete quantum-reference matrix blocks. -/
theorem infinityBody_execute (falseBit : CInputRef ctx .bit) (tag : CWriteRef ctx .bit)
    (zero : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (infinityBody falseBit tag zero output).execute Reference state = state.mapClassical
      (fun entry => (infinityBodyStore falseBit tag zero output entry.1, (entry.2, ((), ())))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (infinityTagOp falseBit tag))
    (repackRawInto (infinityRaw tag zero) output)
    (fun store => (store.applyOp (infinityTagOp falseBit tag), ()))
    (fun store => (repackStore (infinityRaw tag zero) output store, ()))
    (fun reference {_} _ initial =>
      (Circuit.execute_classical_mapClassical (infinityTagOp falseBit tag)
        reference initial).trans (by
          congr 1
          exact Subsingleton.elim _ _))
    (fun reference {_} _ initial => (repackRawInto_execute _ _ reference initial).trans (by
      congr 1
      exact Subsingleton.elim _ _)) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem read_product (store : Store ctx) {first second : CShape}
    (left : CInputRef ctx first) (right : CInputRef ctx second) :
    store.read (.product left right) = .product (store.read left) (store.read right) := rfl

/-- The actual initialized inputs produce the unique tagged zero-coordinate nominal value. -/
theorem infinityBodyStore_eq (falseBit : CInputRef ctx .bit) (tag : CWriteRef ctx .bit)
    (zero : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) (falseRead : store.read falseBit = .bit false)
    (zeroRead : store.read zero = .unsignedWord 0)
    (separate : tag.key ∉ zero.storageKeys) :
    infinityBodyStore falseBit tag zero output store =
      (store.applyOp (infinityTagOp falseBit tag)).write output (.ellipticCurvePoint true 0 0) := by
  have tagRead : (store.applyOp (infinityTagOp falseBit tag)).read (classifierRead tag) =
      .bit true := by
    change (store.applyOp (infinityTagOp falseBit tag)).read
      (.storage (infinityTagOp falseBit tag).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change Resource.BitOpcode.not.eval (store.read falseBit) = _
    rw [falseRead]
    rfl
  have zeroAfter : (store.applyOp (infinityTagOp falseBit tag)).read zero = .unsignedWord 0 :=
    (Store.read_applyOp_of_not_mem_storageKeys store (infinityTagOp falseBit tag)
      zero separate).trans zeroRead
  simp only [infinityBodyStore, repackStore, infinityRaw, read_product, tagRead, zeroAfter]
  rfl

/-- Allocate the original internal sources and write infinity into the supplied destination. -/
def infinityInto (output : CWriteRef ctx (PointShape width)) : Circuit ctx ctx :=
  withCells ctx (infinityShapes width) fun cells _ transport _ =>
    infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
      (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output)

private theorem infinityCells_initialized (cells : Cells ctx (infinityShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    store.read (classifierRead cells.head.ref) = .bit false ∧
      store.read (classifierRead cells.tail.tail.head.ref) = .unsignedWord 0 := by
  cases cells with
  | cons falseBit rest =>
    cases rest with
    | cons tag rest =>
      cases rest with
      | cons zero rest =>
        cases rest
        exact ⟨initialized.1, initialized.2.2.1⟩

private theorem infinityCells_tag_zero_separate (cells : Cells ctx (infinityShapes width))
    (distinct : cells.Distinct) :
    cells.tail.head.ref.key ∉ (classifierRead cells.tail.tail.head.ref).storageKeys := by
  cases cells with
  | cons falseBit rest =>
    cases rest with
    | cons tag rest =>
      cases rest with
      | cons zero rest =>
        cases rest
        have different : tag.ref.key ≠ zero.ref.key := Ne.symm distinct.2.1.1
        change tag.ref.key ∉ (classifierRead zero.ref).storageKeys
        simpa [classifierRead, CInputRef.storageKeys] using different

private theorem infinityCells_tag_avoids {outer : RuntimeCtx kind}
    (cells : Cells ctx (infinityShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {shape : CShape}
    (input : CInputRef outer shape) :
    cells.tail.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  cases cells with
  | cons falseBit rest =>
    cases rest with
    | cons tag rest =>
      cases rest with
      | cons zero rest =>
        cases rest
        exact separated.2.1 input

/-- The actual allocated program changes exactly the caller's destination to infinity. -/
theorem infinityInto_actualRecord (output : CWriteRef ctx (PointShape width)) :
    ∃ step : Store ctx → Store ctx × (infinityInto output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (infinityInto output).execute Reference state = state.mapClassical
          (fun entry => ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, (step before).1 =
        before.write output (.ellipticCurvePoint true 0 0) := by
  apply withCells_actualRecord_initialized_post ctx (infinityShapes width)
    (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
      (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output))
    (fun source target => target = source.write output (.ellipticCurvePoint true 0 0))
  intro inner cells distinct transport separated
  refine ⟨fun store => (infinityBodyStore (classifierRead cells.head.ref) cells.tail.head.ref
    (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output) store, ((), ())), ?_, ?_⟩
  · intro reference history _ initial
    refine (infinityBody_execute _ _ _ _ reference initial).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  intro source before reads initialized
  obtain ⟨falseRead, zeroRead⟩ := infinityCells_initialized cells before initialized
  refine ⟨source.write output (.ellipticCurvePoint true 0 0), rfl, ?_⟩
  have bodyResult := infinityBodyStore_eq (classifierRead cells.head.ref) cells.tail.head.ref
    (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output) before falseRead zeroRead
    (infinityCells_tag_zero_separate cells distinct)
  have afterTag : transport.ReadsAs source
      (before.applyOp (infinityTagOp (classifierRead cells.head.ref) cells.tail.head.ref)) := by
    intro shape input
    exact (Store.read_applyOp_of_not_mem_storageKeys before
      (infinityTagOp (classifierRead cells.head.ref) cells.tail.head.ref)
      (transport.liftInput input) (infinityCells_tag_avoids cells transport separated input)).trans
      (reads input)
  apply (congrArg (transport.ReadsAs (source.write output (.ellipticCurvePoint true 0 0)))
    bodyResult).mpr
  intro shape input
  exact transport.workspaceTransport_readsAs_write afterTag output
    (.ellipticCurvePoint true 0 0) input

/-- This record is certified by the actual interpreter, with its actual lexical path. -/
def infinityStep (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (infinityInto output).Path :=
  Classical.choose (infinityInto_actualRecord output)

/-- Infinity initialization preserves the full quantum reference and actual execution history. -/
theorem infinityInto_execute (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (infinityInto output).execute Reference state = state.mapClassical (fun entry =>
      ((infinityStep output entry.1).1, (entry.2, (infinityStep output entry.1).2))) :=
  (Classical.choose_spec (infinityInto_actualRecord output)).1 Reference state

/-- Every caller store receives the original unique nominal infinity value. -/
theorem infinityStep_store (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    (infinityStep output store).1 = store.write output (.ellipticCurvePoint true 0 0) :=
  (Classical.choose_spec (infinityInto_actualRecord output)).2 store

/-- The actual destination contains the exact original infinity representation. -/
theorem infinityInto_read_output (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    (infinityStep output store).1.read (classifierRead output) = .ellipticCurvePoint true 0 0 := by
  rw [infinityStep_store]
  exact Store.read_write_same store output _

/-- The written actual nominal value represents the semantic point at infinity. -/
theorem infinityInto_represents (spec : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    PointRepresents spec ((infinityStep output store).1.read (classifierRead output)) 0 := by
  rw [infinityInto_read_output]
  exact encodePoint_represents spec 0

/-- Every structural input disjoint from the actual destination retains its original bits. -/
theorem infinityInto_preserves_read (output : CWriteRef ctx (PointShape width)) (store : Store ctx)
    {shape : CShape} (input : CInputRef ctx shape) (separate : output.key ∉ input.storageKeys) :
    (infinityStep output store).1.read input = store.read input := by
  rw [infinityStep_store]
  exact Store.read_write_of_not_mem_storageKeys store output _ input separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
