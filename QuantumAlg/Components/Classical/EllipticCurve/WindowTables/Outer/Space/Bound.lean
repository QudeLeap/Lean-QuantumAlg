/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Live-space composition for the actual table programs

Both resident and auxiliary peaks refer to the original visited contexts.
Sequential stages and finite loops reuse their actual scratch; only a
lexical allocator adds its own live closed shapes. These are derived proof
properties of existing circuits, never constructor-supplied resource fields.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace

open Execution ClassicalWorkspace

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Both actual peaks fit one independent additional capacity over their original caller roles. -/
def Bound (additional : SpacePool model.kind) (code : Circuit model ctx ctx) : Prop :=
  ∀ path, code.peakResidentSpace path ≤ additional + ctx.residentSpace ∧
    code.peakAuxiliarySpace path ≤ additional + ctx.auxiliarySpace

/-- Enlarging an independent native space allowance preserves both actual bounds. -/
lemma Bound.mono {first second : SpacePool model.kind} {code : Circuit model ctx ctx}
    (actual : Bound first code) (larger : first ≤ second) : Bound second code := by
  intro path
  exact ⟨(actual path).1.trans (fun axis => Nat.add_le_add (larger axis) (Nat.le_refl _)),
    (actual path).2.trans (fun axis => Nat.add_le_add (larger axis) (Nat.le_refl _))⟩

/-- One real selected classical instruction uses only the original caller's existing cells. -/
lemma instruction [BitWord.Selected model] {input output : CShape}
    (op : ClassicalOp input output ctx ctx) :
    Bound 0 (BitWord.instruction (execution := model) op) := by
  intro path
  simpa only [BitWord.instruction, zero_add] using
    And.intro (Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := model) op) path).le
      (Circuit.peakAuxiliarySpace_classical
        (BitWord.selectedApplication (execution := model) op) path).le

/-- Sequential actual stages share the same additional allowance rather than adding it twice. -/
lemma seq (additional : SpacePool model.kind) (first second : Circuit model ctx ctx)
    (firstBound : Bound additional first) (secondBound : Bound additional second) :
    Bound additional (first.seq second) := by
  intro path
  exact ⟨(Circuit.peakResidentSpace_seq first second path).le.trans
      (SpacePool.max_le (firstBound path.1).1 (secondBound path.2).1),
    (Circuit.peakAuxiliarySpace_seq first second path).le.trans
      (SpacePool.max_le (firstBound path.1).2 (secondBound path.2).2)⟩

/-- Every original finite component reuses the same actual scratch scope. -/
lemma range (additional : SpacePool model.kind) (count : Nat)
    (body : Fin count → Circuit model ctx ctx)
    (bounded : ∀ index, Bound additional (body index)) :
    Bound additional (Circuit.forRange count body) := by
  intro path
  exact ⟨Circuit.forRange_resident_le count body (additional + ctx.residentSpace)
      (le_add_of_nonneg_left zero_le) (fun index selected => (bounded index selected).1) path,
    Circuit.forRange_auxiliary_le count body (additional + ctx.auxiliarySpace)
      (le_add_of_nonneg_left zero_le) (fun index selected => (bounded index selected).2) path⟩

/-- Every actual lexical cell stays charged through the body and is released before caller exit. -/
lemma allocate {outer : RuntimeCtx model.kind} (transport : Transport outer ctx)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (lift : Transport outer inner) → cells.TransportSeparated lift → Circuit model inner inner)
    (additional : SpacePool model.kind)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (lift : Transport outer inner)
      (separated : cells.TransportSeparated lift),
      Bound additional (body cells distinct lift separated)) :
    Bound ((shapes.map SpacePool.ofShape).sum + additional)
      (withCellsFrom transport shapes body) := by
  intro path
  exact ⟨withCellsFrom_resident_le transport shapes body additional
      (fun cells distinct lift separated selected =>
        (bounded cells distinct lift separated selected).1)
      path,
    withCellsFrom_auxiliary_le transport shapes body additional
      (fun cells distinct lift separated selected =>
        (bounded cells distinct lift separated selected).2)
      path⟩

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace
