/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.Trivial.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Exact actual order-one recovery resources

The original word equality and option pack are the only native events.
The candidate word is allocated before the inner tag and both remain live
through packing. Retention precedes both scopes and keeps the original
optional result live afterward, including when the word width is zero.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native

open Execution ClassicalWorkspace

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The two original native operations retain their exact widths and chronological order. -/
@[expose] public def zeroEvents (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation
      (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal width)),
    .classicalOperation
      (BitWord.selectedCoordinate (execution := model) (.nominalEncoding (.packOption width)))]

/-- Actual allocation and release preserve the original two-event trace. -/
public lemma zeroInto_eventTrace (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).eventTrace path = zeroEvents model width := by
  unfold zeroInto withCells
  have exactTrace := withCellsFrom_property (Transport.id ctx) (zeroShapes width)
    (fun cells _ transport _ =>
      zeroBody (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
        (transport.liftWrite output))
    (fun _ code => ∀ selected : code.Path,
      code.eventTrace selected = zeroEvents model width)
    (fun _ _ _ _ _ available => available)
    (by
      intro inner cells distinct transport separated selected
      simp only [zeroBody, Circuit.eventTrace,
        BitWord.bitWord_instruction_eventTrace, zeroEvents]
      rfl)
  exact exactTrace path

/-- The exact native pool is derived from the same actual two-event trace. -/
public lemma zeroInto_resourcePool (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).resourcePool path = ResourcePool.ofList (zeroEvents model width) := by
  rw [Circuit.resourcePool, zeroInto_eventTrace]

/-- The actual dependency chain charges equality followed by the original option pack. -/
public lemma zeroInto_durationDepth (output : CWriteRef ctx (.option (.unsignedWord width)))
    (duration : Resource.Event model → Nat) (path : (zeroInto output).Path) :
    (zeroInto output).depth duration path =
      duration (.classicalOperation
        (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal width))) +
        duration (.classicalOperation
          (BitWord.selectedCoordinate (execution := model)
            (.nominalEncoding (.packOption width)))) := by
  unfold zeroInto withCells
  have exactDepth := withCellsFrom_property (Transport.id ctx) (zeroShapes width)
    (fun cells _ transport _ =>
      zeroBody (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
        (transport.liftWrite output))
    (fun _ code => ∀ selected : code.Path,
      code.depth duration selected =
        duration (.classicalOperation
          (BitWord.selectedCoordinate (execution := model)
            (.wordBinary .equal width))) +
        duration (.classicalOperation
          (BitWord.selectedCoordinate (execution := model)
            (.nominalEncoding (.packOption width)))))
    (fun _ _ _ _ _ available => available)
    (by
      intro inner cells distinct transport separated selected
      cases selected with
      | mk first second =>
          change
            (BitWord.instruction (execution := model)
              (tagOp (.storage cells.tail.head.ref.toCStorageRef)
                cells.head.ref)).depth duration first +
              (BitWord.instruction (execution := model)
                (packOp (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
                  (transport.liftWrite output))).depth duration second = _
          rw [BitWord.bitWord_instruction_depth,
            BitWord.bitWord_instruction_depth]
          rfl)
  exact exactDepth path

/-- Exactly two actual native instructions execute, also at width zero. -/
public lemma zeroInto_eventCount (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) : ((zeroInto output).eventTrace path).length = 2 := by
  rw [zeroInto_eventTrace]
  rfl

/-- Both temporary cells remain live only inside the reusable order-one scope. -/
public def zeroActiveSpace (width : Nat) : SpacePool model.kind :=
  ((zeroShapes width).map SpacePool.ofShape).sum

private lemma zeroBody_resident_le
    {inner : RuntimeCtx model.kind} (candidate : CInputRef inner (.unsignedWord width))
    (tag : CWriteRef inner .bit) (output : CWriteRef inner (.option (.unsignedWord width)))
    (path : (zeroBody candidate tag output).Path) :
    (zeroBody candidate tag output).peakResidentSpace path ≤ inner.residentSpace := by
  unfold zeroBody at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  exact SpacePool.max_le
    (le_of_eq (Circuit.peakResidentSpace_classical _ path.1))
    (le_of_eq (Circuit.peakResidentSpace_classical _ path.2))

private lemma zeroBody_auxiliary_le
    {inner : RuntimeCtx model.kind} (candidate : CInputRef inner (.unsignedWord width))
    (tag : CWriteRef inner .bit) (output : CWriteRef inner (.option (.unsignedWord width)))
    (path : (zeroBody candidate tag output).Path) :
    (zeroBody candidate tag output).peakAuxiliarySpace path ≤ inner.auxiliarySpace := by
  unfold zeroBody at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  exact SpacePool.max_le
    (le_of_eq (Circuit.peakAuxiliarySpace_classical _ path.1))
    (le_of_eq (Circuit.peakAuxiliarySpace_classical _ path.2))

/-- The order-one routine charges its two actual workspace cells and caller resident state. -/
public lemma zeroInto_resident_le
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).peakResidentSpace path ≤
      zeroActiveSpace (model := model) width + ctx.residentSpace := by
  unfold zeroInto at path ⊢
  unfold zeroActiveSpace
  exact withCellsFrom_resident_le (Transport.id ctx) (zeroShapes width) _ 0 (by
    intro inner cells distinct transport separated selected
    simpa only [zero_add] using zeroBody_resident_le
      (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
        (transport.liftWrite output) selected) path

/-- The same live scope gives the complete auxiliary-role bound. -/
public lemma zeroInto_auxiliary_le
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (path : (zeroInto output).Path) :
    (zeroInto output).peakAuxiliarySpace path ≤
      zeroActiveSpace (model := model) width + ctx.auxiliarySpace := by
  unfold zeroInto at path ⊢
  unfold zeroActiveSpace
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (zeroShapes width) _ 0 (by
    intro inner cells distinct transport separated selected
    simpa only [zero_add] using zeroBody_auxiliary_le
      (.storage cells.tail.head.ref.toCStorageRef) cells.head.ref
        (transport.liftWrite output) selected) path

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.Trivial.Native
