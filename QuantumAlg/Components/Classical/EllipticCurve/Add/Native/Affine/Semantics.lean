/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Values

/-!
# Actual complete caller state of the original affine tail

The real lexical allocation establishes every internal separation and the
false tag. Its actual returned record performs exactly one nominal point
write in the caller Store. Raw finite values, arbitrary operand aliases,
complete quantum references and all prior history are retained.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem affineScratch_keys (cells : Cells ctx (affineShapes width)) :
    (affineScratch cells).keys = cells.keys.reverse := by
  cases cells with
  | cons tag rest =>
    cases rest with
    | cons yOutput rest =>
      cases rest with
      | cons yProduct rest =>
        cases rest with
        | cons xDifference rest =>
          cases rest with
          | cons xOutput rest =>
            cases rest with
            | cons xPartial rest =>
              cases rest with
              | cons slopeSquared rest =>
                cases rest with
                | cons slope rest =>
                  cases rest with
                  | cons coefficient rest =>
                    cases rest
                    rfl

private theorem affineScratch_separation {outer : RuntimeCtx kind}
    (leftX rightX leftY numerator denominator : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (affineShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (affineScratch cells).Separation (transport.liftInput leftX) (transport.liftInput rightX)
      (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) := by
  constructor
  · rw [affineScratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [affineScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) leftX
  · intro key member
    rw [affineScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) rightX
  · intro key member
    rw [affineScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) leftY
  · intro key member
    rw [affineScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) numerator
  · intro key member
    rw [affineScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) denominator

private theorem affineScratch_tag_initialized (cells : Cells ctx (affineShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    store.read (classifierRead (affineScratch cells).tag) = .bit false :=
  Cells.workspaceCells_cellAt_initialized cells store initialized ⟨0, by change 0 < 9; decide⟩

private theorem affineArithmeticStore_readsAs {outer : RuntimeCtx kind}
    (cells : Cells ctx (affineShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (source : Store outer) (before : Store ctx)
    (reads : transport.ReadsAs source before) (values : AffineValues width) :
    transport.ReadsAs source (affineArithmeticStore (affineScratch cells) values before) := by
  intro shape input
  refine (affineArithmeticStore_preserves _ _ _ (transport.liftInput input) ?_).trans (reads input)
  intro key member
  rw [affineScratch_keys] at member
  exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
    (List.mem_reverse.mp member) input

/-- The actual caller destination receives the original closed finite result and initialized tag. -/
def affineOutputValue (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CShape.Word width) :
    CShape.Value (PointShape width) :=
  (affineValues spec leftX rightX leftY numerator denominator).point (.bit false)

/-- Real allocation and release leave exactly one caller write, with no workspace premise. -/
theorem affineInto_completeRecord (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) :
    ∃ record : Store ctx → Store ctx ×
        (affineInto spec leftX rightX leftY numerator denominator output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (affineInto spec leftX rightX leftY numerator denominator output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ store : Store ctx, (record store).1 = store.write output
        (affineOutputValue spec (store.read leftX) (store.read rightX) (store.read leftY)
          (store.read numerator) (store.read denominator)) := by
  apply withCells_actualRecord_initialized_post ctx (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (fun source target => target = source.write output
      (affineOutputValue spec (source.read leftX) (source.read rightX) (source.read leftY)
        (source.read numerator) (source.read denominator)))
  intro inner cells distinct transport separated
  refine ⟨affineBodyStep spec (transport.liftInput leftX) (transport.liftInput rightX)
    (transport.liftInput leftY) (transport.liftInput numerator) (transport.liftInput denominator)
    (affineScratch cells) (transport.liftWrite output), affineBody_execute _ _ _ _ _ _ _ _, ?_⟩
  intro source before reads initialized
  let values := affineValues spec (source.read leftX) (source.read rightX) (source.read leftY)
    (source.read numerator) (source.read denominator)
  refine ⟨source.write output (values.point (.bit false)), rfl, ?_⟩
  rw [affineBodyStep_store, affineBodyStore_values _ _ _ _ _ _ _ _
    (affineScratch_separation leftX rightX leftY numerator denominator cells distinct
      transport separated), reads leftX, reads rightX, reads leftY, reads numerator,
    reads denominator, affineScratch_tag_initialized cells before initialized]
  exact Transport.workspaceTransport_readsAs_write transport
    (affineArithmeticStore_readsAs cells transport separated source before reads values)
    output (values.point (.bit false))

/-- The exact actual path and caller Store of the original total affine tail. -/
def affineIntoStep (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx ×
      (affineInto spec leftX rightX leftY numerator denominator output).Path :=
  Classical.choose (affineInto_completeRecord spec leftX rightX leftY numerator denominator output)

/-- Complete quantum-reference blocks and history follow the same actual selected tail record. -/
theorem affineInto_execute (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (affineInto spec leftX rightX leftY numerator denominator output).execute Reference state =
      state.mapClassical (fun entry =>
        ((affineIntoStep spec leftX rightX leftY numerator denominator output entry.1).1,
          (entry.2, (affineIntoStep spec leftX rightX leftY numerator denominator output
            entry.1).2))) :=
  (Classical.choose_spec (affineInto_completeRecord spec leftX rightX leftY numerator denominator
    output)).1 Reference state

/-- Every raw input gives exactly the original finite nominal point in the sole caller write. -/
theorem affineIntoStep_store (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    (affineIntoStep spec leftX rightX leftY numerator denominator output store).1 =
      store.write output (affineOutputValue spec (store.read leftX) (store.read rightX)
        (store.read leftY) (store.read numerator) (store.read denominator)) :=
  (Classical.choose_spec (affineInto_completeRecord spec leftX rightX leftY numerator denominator
    output)).2 store

/-- Every structural read outside the caller result remains bitwise unchanged. -/
theorem affineInto_preserves_read (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : output.key ∉ input.storageKeys) :
    (affineIntoStep spec leftX rightX leftY numerator denominator output store).1.read input =
      store.read input := by
  rw [affineIntoStep_store]
  exact Store.read_write_of_not_mem_storageKeys store output _ input separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
