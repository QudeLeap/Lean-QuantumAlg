/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Scope
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Resources.Space
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Resources

/-!
# Actual feedback-scope storage and resource composition

The real allocator retains all caller cells and every physical quantum wire.
Its native event ledger and dependency depth are those of the actual body;
its live classical shape is added exactly once around that body.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution ClassicalWorkspace

/-- The actual declared feedback shapes, before choosing any caller context. -/
def frameSpace (kind : ProblemKind) (wordWidth parityCount : Nat) : SpacePool kind :=
  ((shapes wordWidth parityCount).map SpacePool.ofShape).sum

private lemma finiteTwo_bits : CShape.bitWidth (.finite 2) = 1 := by decide

private lemma cellShape_bits (wordWidth parityCount : Nat)
    (index : Fin (cellCount wordWidth parityCount)) :
    (cellShape wordWidth parityCount index).bitWidth =
      if index.val = wordWidth then wordWidth else 1 := by
  by_cases before : index.val < wordWidth
  · have different : index.val ≠ wordWidth := Nat.ne_of_lt before
    simp only [cellShape, if_pos before, if_neg different, finiteTwo_bits]
  · by_cases same : index.val = wordWidth
    · simp only [cellShape, if_neg before, if_pos same, CShape.bitWidth_bits]
    · simp only [cellShape, if_neg before, if_neg same, CShape.bitWidth_bit]

private lemma shape_bits_sum (wordWidth parityCount : Nat) :
    (∑ index : Fin (cellCount wordWidth parityCount),
      (cellShape wordWidth parityCount index).bitWidth) = 2 * wordWidth + parityCount + 1 := by
  let mask : Fin (wordWidth + parityCount + 1 + 1) := ⟨wordWidth, by omega⟩
  change (∑ index : Fin (wordWidth + parityCount + 1 + 1),
    (cellShape wordWidth parityCount index).bitWidth) = _
  rw [Fin.sum_univ_succAbove _ mask]
  have selected : (cellShape wordWidth parityCount mask).bitWidth = wordWidth :=
    (cellShape_bits wordWidth parityCount mask).trans (if_pos rfl)
  have remaining : ∀ index : Fin (wordWidth + parityCount + 1),
      (cellShape wordWidth parityCount (mask.succAbove index)).bitWidth = 1 := by
    intro index
    have different : (mask.succAbove index).val ≠ wordWidth := by
      intro same
      exact (Fin.succAbove_ne mask index) (Fin.ext same)
    exact (cellShape_bits wordWidth parityCount (mask.succAbove index)).trans
      (if_neg different)
  simp only [selected, remaining, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_one]
  omega

private lemma frameSpace_evaluation (kind : ProblemKind) (wordWidth parityCount : Nat)
    (axis : SpaceAxis kind) :
    frameSpace kind wordWidth parityCount axis =
      ∑ index : Fin (cellCount wordWidth parityCount),
        SpacePool.ofShape (cellShape wordWidth parityCount index) axis := by
  simp only [frameSpace, shapes, List.map_ofFn, List.sum_ofFn, Finset.sum_apply,
    Function.comp_apply]

/-- The packed mask, all finite outputs, parity cells and temporary bit are fully charged. -/
lemma frameSpace_classicalBits (kind : ProblemKind) (wordWidth parityCount : Nat) :
    frameSpace kind wordWidth parityCount .classicalBits = 2 * wordWidth + parityCount + 1 :=
  (frameSpace_evaluation kind wordWidth parityCount .classicalBits).trans
    (shape_bits_sum wordWidth parityCount)

/-- These actual classical cells add no quantum system of any positive dimension. -/
lemma frameSpace_quantumSystems (wordWidth parityCount : Nat) (dimension : ℕ+) :
    frameSpace .quantum wordWidth parityCount (.quantumSystems dimension) = 0 := by
  rw [frameSpace_evaluation]
  simp only [SpacePool.ofShape, Finset.sum_const_zero]

section Scope

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (wordWidth parityCount : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (frame : Frame inner wordWidth parityCount) → CallerFree frame transport →
      Circuit model inner inner)

/-- Every actual scoped path has the body's independently proved scalar event bound. -/
lemma withFrame_weightedCount_le (weight : Resource.Event model → Nat) (limit : Nat)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (frame : Frame inner wordWidth parityCount) (fresh : CallerFree frame transport)
      (path : (body transport same frame fresh).Path),
      ResourcePool.weightedCount weight ((body transport same frame fresh).resourcePool path) ≤
        limit)
    (path : (withFrame ctx wordWidth parityCount body).Path) :
    ResourcePool.weightedCount weight
      ((withFrame ctx wordWidth parityCount body).resourcePool path) ≤ limit := by
  unfold withFrame withCellsWithQuantumWires
  apply withCellsWithQuantumWiresFrom_weightedCount_le
    (Transport.id ctx) rfl (shapes wordWidth parityCount) _ weight limit ?_ path
  intro inner cells distinct transport separated same selected
  exact bounded transport _ _ _ selected

/-- Every native event coordinate keeps its actual body bound through the same scope. -/
lemma withFrame_count_le (event : Resource.Event model) (limit : Nat)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (frame : Frame inner wordWidth parityCount) (fresh : CallerFree frame transport)
      (path : (body transport same frame fresh).Path),
      ResourcePool.count event ((body transport same frame fresh).resourcePool path) ≤ limit)
    (path : (withFrame ctx wordWidth parityCount body).Path) :
    ResourcePool.count event ((withFrame ctx wordWidth parityCount body).resourcePool path) ≤
      limit := by
  unfold withFrame withCellsWithQuantumWires
  exact (withCellsWithQuantumWiresFrom_property
    (Transport.id ctx) rfl (shapes wordWidth parityCount)
    (fun cells distinct transport separated same =>
      body transport (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct transport separated))
    (fun {inner} _ _ (code : Circuit model inner inner) =>
      ∀ selected, ResourcePool.count event (code.resourcePool selected) ≤ limit)
    (fun _ _ _ _ _ _ available => available)
    (fun cells distinct transport separated same => bounded transport
      (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
      (ofCells_callerFree cells distinct transport separated))) path

/-- Exact event multiplicity survives allocation and release of the real feedback cells. -/
lemma withFrame_event_count (event : Resource.Event model) (amount : Nat)
    (counted : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (frame : Frame inner wordWidth parityCount) (fresh : CallerFree frame transport)
      (path : (body transport same frame fresh).Path),
      ResourcePool.count event ((body transport same frame fresh).resourcePool path) = amount)
    (path : (withFrame ctx wordWidth parityCount body).Path) :
    ResourcePool.count event ((withFrame ctx wordWidth parityCount body).resourcePool path) =
      amount := by
  unfold withFrame withCellsWithQuantumWires
  exact (withCellsWithQuantumWiresFrom_property
    (Transport.id ctx) rfl (shapes wordWidth parityCount)
    (fun cells distinct transport separated same =>
      body transport (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct transport separated))
    (fun {inner} _ _ (code : Circuit model inner inner) =>
      ∀ selected, ResourcePool.count event (code.resourcePool selected) = amount)
    (fun _ _ _ _ _ _ available => available)
    (fun cells distinct transport separated same => counted transport
      (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
      (ofCells_callerFree cells distinct transport separated))) path

/-- The same actual dependency depth passes through the classical feedback scope. -/
lemma withFrame_depth_le (duration : Resource.Event model → Nat) (limit : Nat)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (frame : Frame inner wordWidth parityCount) (fresh : CallerFree frame transport)
      (path : (body transport same frame fresh).Path),
      (body transport same frame fresh).depth duration path ≤ limit)
    (path : (withFrame ctx wordWidth parityCount body).Path) :
    (withFrame ctx wordWidth parityCount body).depth duration path ≤ limit := by
  unfold withFrame withCellsWithQuantumWires
  apply withCellsWithQuantumWiresFrom_depth_le
    (Transport.id ctx) rfl (shapes wordWidth parityCount) _ duration limit ?_ path
  intro inner cells distinct transport separated same selected
  exact bounded transport _ _ _ selected

/-- The real feedback shape coexists with body scratch and the complete original caller pool. -/
lemma withFrame_peak_le (projection : RuntimeCtx model.kind → SpacePool model.kind)
    (workspaceSpace : ∀ (inner : RuntimeCtx model.kind) (key : StorageKey)
      (shape : CShape) (fresh : key ∉ inner.keys),
      projection (inner.addWorkspace key shape fresh) = SpacePool.ofShape shape + projection inner)
    (additional : SpacePool model.kind)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (frame : Frame inner wordWidth parityCount) (fresh : CallerFree frame transport)
      (path : (body transport same frame fresh).Path),
      Circuit.peak projection ((body transport same frame fresh).visitedContexts path) ≤
        additional + projection inner)
    (path : (withFrame ctx wordWidth parityCount body).Path) :
    Circuit.peak projection ((withFrame ctx wordWidth parityCount body).visitedContexts path) ≤
      frameSpace model.kind wordWidth parityCount + additional + projection ctx := by
  unfold withFrame withCellsWithQuantumWires frameSpace
  apply Driver.quantumScopes_peak_le (Transport.id ctx) rfl (shapes wordWidth parityCount)
    _ projection workspaceSpace additional ?_ path
  intro inner cells distinct transport separated same selected
  exact bounded transport _ _ _ selected

end Scope

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
