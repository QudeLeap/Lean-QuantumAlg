/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic

/-!
# Actual complete Store returned by the original generic finite arm

Both original subtractions and the shared original affine tail act on their
actual predecessor stores. All intermediate cells are allocated internally;
the returned caller Store contains exactly one nominal result write.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact finite generic output, including the original total coefficient on every raw input. -/
def genericOutputValue (spec : ModulusSpec width)
    (left right : CShape.Value (PointEquality.RawPointShape width)) :
    CShape.Value (PointShape width) :=
  affineOutputValue spec left.second.first right.second.first left.second.second
    (Field.Native.subtractionWord spec right.second.second left.second.second)
    (Field.Native.subtractionWord spec right.second.first left.second.first)

/-- Only the two internally allocated original prefix cells require separation. -/
structure GenericSeparation
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width)) : Prop where
  distinct : numerator.key ≠ denominator.key
  numerator : ∀ input ∈ [leftX, leftY, rightX, rightY], numerator.key ∉ input.storageKeys
  denominator : ∀ input ∈ [leftX, leftY, rightX, rightY], denominator.key ∉ input.storageKeys

/-- Both actual prefix results and the total affine result appear in the complete returned Store. -/
theorem genericBodyStep_store (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (separate : GenericSeparation leftX leftY rightX rightY numerator denominator)
    (store : Store ctx) :
    (genericBodyStep spec leftX leftY rightX rightY numerator denominator output store).1 =
      ((store.write numerator (Field.Native.subtractionWord spec
        (store.read rightY) (store.read leftY))).write denominator
          (Field.Native.subtractionWord spec (store.read rightX) (store.read leftX))).write output
            (affineOutputValue spec (store.read leftX) (store.read rightX) (store.read leftY)
              (Field.Native.subtractionWord spec (store.read rightY) (store.read leftY))
              (Field.Native.subtractionWord spec (store.read rightX) (store.read leftX))) := by
  have nx := separate.numerator leftX (by simp)
  have ny := separate.numerator leftY (by simp)
  have nr := separate.numerator rightX (by simp)
  have dx := separate.denominator leftX (by simp)
  have dy := separate.denominator leftY (by simp)
  have dr := separate.denominator rightX (by simp)
  have dn := Ne.symm separate.distinct
  rw [genericBodyStep, Circuit.sequenceRecord_store, Circuit.sequenceRecord_store]
  rw [Field.Native.subIntoWordStep_store, Field.Native.subIntoWordStep_store, affineIntoStep_store]
  simp only [classifierRead, Store.read_write_same,
    Store.read_write_of_not_mem_storageKeys _ numerator _ leftX nx,
    Store.read_write_of_not_mem_storageKeys _ numerator _ leftY ny,
    Store.read_write_of_not_mem_storageKeys _ numerator _ rightX nr,
    Store.read_write_of_not_mem_storageKeys _ denominator _ leftX dx,
    Store.read_write_of_not_mem_storageKeys _ denominator _ leftY dy,
    Store.read_write_of_not_mem_storageKeys _ denominator _ rightX dr,
    Store.read_write_other _ denominator numerator.toCStorageRef _ dn]

private theorem genericCells_distinct (cells : Cells ctx (genericShapes width))
    (distinct : cells.Distinct) : cells.tail.head.ref.key ≠ cells.head.ref.key := by
  cases cells with
  | cons denominator rest =>
    cases rest with
    | cons numerator rest =>
      cases rest
      exact distinct.1.1

private theorem genericCells_numerator_avoids {outer : RuntimeCtx kind}
    (cells : Cells ctx (genericShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {shape : CShape}
    (input : CInputRef outer shape) :
    cells.tail.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  apply Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
  cases cells with
  | cons denominator rest =>
    cases rest with
    | cons numerator rest =>
      cases rest
      simp [Cells.keys, Cells.tail, Cells.head]

private theorem genericCells_denominator_avoids {outer : RuntimeCtx kind}
    (cells : Cells ctx (genericShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {shape : CShape}
    (input : CInputRef outer shape) :
    cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  apply Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
  cases cells with
  | cons denominator rest => simp [Cells.keys, Cells.head]

private theorem genericCells_separation {outer : RuntimeCtx kind}
    (leftX leftY rightX rightY : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (genericShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    GenericSeparation (transport.liftInput leftX) (transport.liftInput leftY)
      (transport.liftInput rightX) (transport.liftInput rightY)
      cells.tail.head.ref cells.head.ref := by
  refine ⟨genericCells_distinct cells distinct, ?_, ?_⟩
  · intro input member
    rcases List.mem_cons.mp member with rfl | member
    · exact genericCells_numerator_avoids cells transport separated leftX
    rcases List.mem_cons.mp member with rfl | member
    · exact genericCells_numerator_avoids cells transport separated leftY
    rcases List.mem_cons.mp member with rfl | member
    · exact genericCells_numerator_avoids cells transport separated rightX
    have same := List.mem_singleton.mp member
    subst input
    exact genericCells_numerator_avoids cells transport separated rightY
  · intro input member
    rcases List.mem_cons.mp member with rfl | member
    · exact genericCells_denominator_avoids cells transport separated leftX
    rcases List.mem_cons.mp member with rfl | member
    · exact genericCells_denominator_avoids cells transport separated leftY
    rcases List.mem_cons.mp member with rfl | member
    · exact genericCells_denominator_avoids cells transport separated rightX
    have same := List.mem_singleton.mp member
    subst input
    exact genericCells_denominator_avoids cells transport separated rightY

/-- Actual allocation supplies all prefix conditions and returns the sole original caller write. -/
theorem genericInto_completeRecord (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) :
    ∃ record : Store ctx → Store ctx × (genericInto spec left right output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (genericInto spec left right output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ store : Store ctx, (record store).1 = store.write output
        (genericOutputValue spec (store.read left) (store.read right)) := by
  apply withCells_actualRecord_initialized_post ctx (genericShapes width)
    (fun cells _ transport _ => genericBody spec
      (transport.liftInput (.first (.second left)))
      (transport.liftInput (.second (.second left)))
      (transport.liftInput (.first (.second right)))
      (transport.liftInput (.second (.second right))) cells.tail.head.ref cells.head.ref
      (transport.liftWrite output))
    (fun source target => target = source.write output
      (genericOutputValue spec (source.read left) (source.read right)))
  intro inner cells distinct transport separated
  refine ⟨genericBodyStep _ _ _ _ _ _ _ _, genericBody_execute _ _ _ _ _ _ _ _, ?_⟩
  intro source before reads _initialized
  let numerator := Field.Native.subtractionWord spec (source.read right).second.second
    (source.read left).second.second
  let denominator := Field.Native.subtractionWord spec (source.read right).second.first
    (source.read left).second.first
  have prefixReads : transport.ReadsAs source
      ((before.write cells.tail.head.ref numerator).write cells.head.ref denominator) := by
    intro shape input
    rw [Store.read_write_of_not_mem_storageKeys _ cells.head.ref _
      (transport.liftInput input)
      (genericCells_denominator_avoids cells transport separated input),
      Store.read_write_of_not_mem_storageKeys _ cells.tail.head.ref _ (transport.liftInput input)
        (genericCells_numerator_avoids cells transport separated input)]
    exact reads input
  refine ⟨source.write output (genericOutputValue spec (source.read left) (source.read right)),
    rfl, ?_⟩
  rw [genericBodyStep_store _ _ _ _ _ _ _ _
    (genericCells_separation (.first (.second left)) (.second (.second left))
      (.first (.second right)) (.second (.second right)) cells distinct transport separated),
    reads (.first (.second left)), reads (.second (.second left)),
    reads (.first (.second right)), reads (.second (.second right))]
  exact Transport.workspaceTransport_readsAs_write transport prefixReads output
    (genericOutputValue spec (source.read left) (source.read right))

/-- Actual generic path and complete caller Store, including all raw exceptional inputs. -/
def genericIntoStep (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (genericInto spec left right output).Path :=
  Classical.choose (genericInto_completeRecord spec left right output)

/-- Actual reference-preserving generic execution follows that same complete native record. -/
theorem genericInto_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (genericInto spec left right output).execute Reference state = state.mapClassical (fun entry =>
      ((genericIntoStep spec left right output entry.1).1,
        (entry.2, (genericIntoStep spec left right output entry.1).2))) :=
  (Classical.choose_spec (genericInto_completeRecord spec left right output)).1 Reference state

/-- The actual generic return changes precisely the chosen nominal result cell. -/
theorem genericIntoStep_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    (genericIntoStep spec left right output store).1 =
      store.write output (genericOutputValue spec (store.read left) (store.read right)) :=
  (Classical.choose_spec (genericInto_completeRecord spec left right output)).2 store

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
