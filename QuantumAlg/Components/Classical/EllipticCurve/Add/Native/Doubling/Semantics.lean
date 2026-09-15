/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling.Values

/-!
# Actual caller Store returned by the original doubling arm

Six real prefix allocations supply all separation for the original arithmetic
and curve-coefficient loader. The shared actual affine tail then writes the
sole caller result. All lexical cells are released through that same record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem doublingScratch_keys (cells : Cells ctx (doublingShapes width)) :
    (doublingScratch cells).keys = cells.keys.reverse := by
  cases cells with
  | cons denominator rest =>
    cases rest with
    | cons numerator rest =>
      cases rest with
      | cons a rest =>
        cases rest with
        | cons tripled rest =>
          cases rest with
          | cons doubled rest =>
            cases rest with
            | cons square rest =>
              cases rest
              rfl

private theorem doublingScratch_separation {outer : RuntimeCtx kind}
    (pointX pointY : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (doublingShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (doublingScratch cells).Separation (transport.liftInput pointX)
      (transport.liftInput pointY) := by
  constructor
  · rw [doublingScratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [doublingScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) pointX
  · intro key member
    rw [doublingScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) pointY

private theorem doublingArithmeticStore_readsAs {outer : RuntimeCtx kind}
    (cells : Cells ctx (doublingShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (source : Store outer) (before : Store ctx)
    (reads : transport.ReadsAs source before) (values : DoublingValues width) :
    transport.ReadsAs source (doublingArithmeticStore (doublingScratch cells) values before) := by
  intro shape input
  refine (doublingArithmeticStore_preserves _ _ _ (transport.liftInput input) ?_).trans
    (reads input)
  intro key member
  rw [doublingScratch_keys] at member
  exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
    (List.mem_reverse.mp member) input

/-- The actual complete original doubling arm returns exactly one caller point write. -/
theorem doublingInto_completeRecord (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) :
    ∃ record : Store ctx → Store ctx × (doublingInto spec point output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (doublingInto spec point output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ store : Store ctx, (record store).1 = store.write output
        (doublingOutputValue spec (store.read point)) := by
  apply withCells_actualRecord_initialized_post ctx (doublingShapes width)
    (fun cells _ transport _ => doublingBody spec
      (transport.liftInput (.first (.second point)))
      (transport.liftInput (.second (.second point))) (doublingScratch cells)
      (transport.liftWrite output))
    (fun source target => target = source.write output
      (doublingOutputValue spec (source.read point)))
  intro inner cells distinct transport separated
  refine ⟨doublingBodyStep _ _ _ _ _, doublingBody_execute _ _ _ _ _, ?_⟩
  intro source before reads _initialized
  let values := doublingValues spec (source.read point).second.first
    (source.read point).second.second
  refine ⟨source.write output (doublingOutputValue spec (source.read point)), rfl, ?_⟩
  rw [doublingBodyStep_store, doublingBodyStore_values _ _ _ _ _
    (doublingScratch_separation (.first (.second point)) (.second (.second point))
      cells distinct transport separated), reads (.first (.second point)),
    reads (.second (.second point))]
  exact Transport.workspaceTransport_readsAs_write transport
    (doublingArithmeticStore_readsAs cells transport separated source before reads values)
    output (doublingOutputValue spec (source.read point))

/-- The actual original doubling path and complete returned caller Store. -/
def doublingIntoStep (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (doublingInto spec point output).Path :=
  Classical.choose (doublingInto_completeRecord spec point output)

/-- Actual doubling retains every complete quantum-reference block and original history. -/
theorem doublingInto_execute (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (doublingInto spec point output).execute Reference state = state.mapClassical (fun entry =>
      ((doublingIntoStep spec point output entry.1).1,
        (entry.2, (doublingIntoStep spec point output entry.1).2))) :=
  (Classical.choose_spec (doublingInto_completeRecord spec point output)).1 Reference state

/-- Every raw snapshot yields exactly the original finite nominal result in the destination. -/
theorem doublingIntoStep_store (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    (doublingIntoStep spec point output store).1 =
      store.write output (doublingOutputValue spec (store.read point)) :=
  (Classical.choose_spec (doublingInto_completeRecord spec point output)).2 store

/-- All actual structural reads outside the caller destination remain unchanged. -/
theorem doublingInto_preserves_read (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : output.key ∉ input.storageKeys) :
    (doublingIntoStep spec point output store).1.read input = store.read input := by
  rw [doublingIntoStep_store]
  exact Store.read_write_of_not_mem_storageKeys store output _ input separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
