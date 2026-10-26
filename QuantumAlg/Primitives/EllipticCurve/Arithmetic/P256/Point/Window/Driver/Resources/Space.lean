/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Space.Builder
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Actual table-array and builder-scratch lifetimes around one complete point

The same five classical arrays coexist with the actual builder scratch.
The allocation-free point body retains the entire caller context. Classical
workspace allocation preserves every physical wire and its original role.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Driver

noncomputable section

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

private lemma quantumScopes_peak_le {model : ExecutionModel}
    {outer ctx : RuntimeCtx model.kind} (transport : Transport outer ctx)
    (same : outer.quantumWires = ctx.quantumWires) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
      outer.quantumWires = inner.quantumWires → Circuit model inner inner)
    (projection : RuntimeCtx model.kind → SpacePool model.kind)
    (workspaceSpace : ∀ (inner : RuntimeCtx model.kind) (key : StorageKey)
      (shape : CShape) (fresh : key ∉ inner.keys),
      projection (inner.addWorkspace key shape fresh) = SpacePool.ofShape shape + projection inner)
    (additional : SpacePool model.kind)
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires)
      (path : (body cells distinct innerTransport separated innerSame).Path),
      Circuit.peak projection
        ((body cells distinct innerTransport separated innerSame).visitedContexts path) ≤
          additional + projection inner)
    (path : (withCellsWithQuantumWiresFrom transport same shapes body).Path) :
    Circuit.peak projection
      ((withCellsWithQuantumWiresFrom transport same shapes body).visitedContexts path) ≤
        (shapes.map SpacePool.ofShape).sum + additional + projection ctx := by
  induction shapes generalizing ctx additional with
  | nil =>
      simpa only [withCellsWithQuantumWiresFrom, List.map_nil, List.sum_nil, zero_add]
        using bodyBound _ _ _ _ _ path
  | cons shape shapes inductionHypothesis =>
      dsimp only [withCellsWithQuantumWiresFrom] at path ⊢
      refine (inductionHypothesis transport same _
        (SpacePool.ofShape shape + additional) ?_ path).trans ?_
      · intro inner cells distinct innerTransport separated innerSame selected
        rw [ClassicalWorkspace.peak_workspace]
        refine SpacePool.max_le (le_add_of_nonneg_left zero_le) ?_
        have inside := bodyBound _ _ _ _ _ selected
        simpa only [workspaceSpace, add_assoc, add_left_comm, add_comm] using inside
      · exact le_of_eq (by simp only [List.map_cons, List.sum_cons]; ac_rfl)

namespace Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Driver.Parameters ctx)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256)
    (spec : ModulusSpec 256) (row : Fin 34)

/-- Independent actual peak allowance for the five live arrays and reused classical arithmetic. -/
def additionalSpace : SpacePool .quantum :=
  ClassicalRoutines.EllipticCurve.WindowTables.Outer.tableSpace .quantum 256
    (2 ^ (parameters.highRemaining + parameters.lowWidth + 1)) +
      ClassicalRoutines.EllipticCurve.WindowTables.Outer.coefficientScratchSpace .quantum 256

lemma circuit_resident_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    (Driver.circuit parameters frame spec row).peakResidentSpace path ≤
      parameters.additionalSpace + ctx.residentSpace := by
  unfold Driver.circuit
    ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame.withConstructedQuantumTables
    withCellsWithQuantumWires additionalSpace
    ClassicalRoutines.EllipticCurve.WindowTables.Outer.tableSpace
  refine quantumScopes_peak_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (Transport.id ctx) rfl _ _ RuntimeCtx.residentSpace
    RuntimeCtx.residentSpace_addWorkspace _ ?_ path
  intro inner cells distinct lift separated same selected
  let table := frame.tableFrame lift cells distinct separated row
  change ((table.circuit (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    spec).seq _).peakResidentSpace selected ≤ _
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · exact (ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace.builder
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      table spec selected.1).1
  · rw [Circuit.peakResidentSpace_embed]
    exact le_add_of_nonneg_left zero_le

lemma circuit_auxiliary_le
    (path : (Driver.circuit (services := services) parameters frame spec row).Path) :
    (Driver.circuit parameters frame spec row).peakAuxiliarySpace path ≤
      parameters.additionalSpace + ctx.auxiliarySpace := by
  unfold Driver.circuit
    ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame.withConstructedQuantumTables
    withCellsWithQuantumWires additionalSpace
    ClassicalRoutines.EllipticCurve.WindowTables.Outer.tableSpace
  refine quantumScopes_peak_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (Transport.id ctx) rfl _ _ RuntimeCtx.auxiliarySpace
    RuntimeCtx.auxiliarySpace_addWorkspace _ ?_ path
  intro inner cells distinct lift separated same selected
  let table := frame.tableFrame lift cells distinct separated row
  change ((table.circuit (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    spec).seq _).peakAuxiliarySpace selected ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · exact (ClassicalRoutines.EllipticCurve.WindowTables.Outer.LiveSpace.builder
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      table spec selected.1).2
  · rw [Circuit.peakAuxiliarySpace_embed]
    exact le_add_of_nonneg_left zero_le

end Parameters

end

end Driver

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
