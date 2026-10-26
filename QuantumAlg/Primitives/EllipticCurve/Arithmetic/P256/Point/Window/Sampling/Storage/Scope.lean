/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum

/-!
# A real lexical feedback scope preserving the entire physical quantum bank

The continuation receives references to the actual freshly allocated cells.
Freshness protects every original caller read, including the retained Fourier
results. The scope surrounds only a context-preserving body; retained output
allocation belongs after its actual exit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

open Execution ClassicalWorkspace

/-- Every fresh scratch key avoids all structurally transported original caller reads. -/
structure CallerFree {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {wordWidth parityCount : Nat} (frame : Frame inner wordWidth parityCount)
    (transport : Transport outer inner) : Prop where
  output : ∀ index {shape : CShape} (input : CInputRef outer shape),
    (frame.output index).key ∉ (transport.liftInput input).storageKeys
  mask : ∀ {shape : CShape} (input : CInputRef outer shape),
    frame.mask.key ∉ (transport.liftInput input).storageKeys
  parity : ∀ index {shape : CShape} (input : CInputRef outer shape),
    (frame.parity index).key ∉ (transport.liftInput input).storageKeys
  temporary : ∀ {shape : CShape} (input : CInputRef outer shape),
    frame.temporary.key ∉ (transport.liftInput input).storageKeys

private lemma refAt_free {kind : ProblemKind} {outer inner : RuntimeCtx kind} {count : Nat}
    (shape : Fin count → CShape) (cells : Cells inner (List.ofFn shape))
    (transport : Transport outer inner) (separated : cells.TransportSeparated transport)
    (index : Fin count) {observed : CShape} (input : CInputRef outer observed) :
    (refAt shape cells index).key ∉ (transport.liftInput input).storageKeys := by
  rw [refAt_key]
  exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
    (workspaceCells_cellAt_key_mem_keys cells (listedIndex shape index)) input

/-- The actual allocator discharges caller protection without an input-state premise. -/
lemma ofCells_callerFree {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {wordWidth parityCount : Nat} (cells : Cells inner (shapes wordWidth parityCount))
    (distinct : cells.Distinct) (transport : Transport outer inner)
    (separated : cells.TransportSeparated transport) :
    CallerFree (Frame.ofCells cells distinct) transport := by
  constructor
  · intro index shape input
    simp only [Frame.ofCells, Frame.outputOfCells, castWrite_key]
    exact refAt_free (cellShape wordWidth parityCount) cells transport separated _ input
  · intro shape input
    simp only [Frame.ofCells, Frame.maskOfCells, castWrite_key]
    exact refAt_free (cellShape wordWidth parityCount) cells transport separated _ input
  · intro index shape input
    simp only [Frame.ofCells, Frame.parityOfCells, castWrite_key]
    exact refAt_free (cellShape wordWidth parityCount) cells transport separated _ input
  · intro shape input
    simp only [Frame.ofCells, Frame.temporaryOfCells, castWrite_key]
    exact refAt_free (cellShape wordWidth parityCount) cells transport separated _ input

/-- Allocate all feedback storage once around a literal fixed-context execution. -/
def withFrame {model : ExecutionModel} (ctx : RuntimeCtx model.kind)
    (wordWidth parityCount : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (transport : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (frame : Frame inner wordWidth parityCount) → CallerFree frame transport →
      Circuit model inner inner) : Circuit model ctx ctx :=
  withCellsWithQuantumWires ctx (shapes wordWidth parityCount)
    fun cells distinct transport separated same =>
      body transport (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct transport separated)

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
