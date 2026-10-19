/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Exact physical space of the three actual core packages

The independent allocation budget sums the declared shared, slot and state
shapes. Each actual path retains the caller context and adds this budget to
any further space required by the body.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace

open Execution.ClassicalWorkspace

/-- Exact simultaneous space of the actual shared, slot and state shape lists. -/
def allocationSpace {kind : ProblemKind} (N : Nat) : SpacePool kind :=
  ((LatticeCandidateSharedWorkspaceLayout.shapes N).map SpacePool.ofShape).sum +
    ((LatticeCandidateSlotWorkspaceLayout.shapes N).map SpacePool.ofShape).sum +
    ((LatticePairStateWorkspaceLayout.shapes N).map SpacePool.ofShape).sum

/-- Independent classical-bit formula for the three core packages. -/
def allocationBits (N : Nat) : Nat :=
  38 * LatticeWideLllMachine.Width N + 5 * modulusBits N + 4 * measurementBits N +
    2 * BatchMachine.JWidth N + 2 * BatchMachine.KWidth N + 13

private lemma coreSpaceArithmetic (width modulus measured jWidth kWidth : Nat) :
    (([.unsignedWord width, .unsignedWord width, .canonicalResidue modulus,
      .unsignedWord (modulus + 1), .unsignedWord modulus, .unsignedWord modulus].map
        CShape.bitWidth).sum + (21 * width + modulus + 10) +
      ([.unsignedWord measured, .unsignedWord measured,
        .unsignedWord jWidth, .unsignedWord kWidth,
        .unsignedWord measured, .unsignedWord measured,
        .unsignedWord jWidth, .unsignedWord kWidth,
        .unsignedWord width, .unsignedWord width, .unsignedWord width,
        .unsignedWord width, .unsignedWord width, .unsignedWord width,
        .unsignedWord width, .unsignedWord width, .unsignedWord width,
        .unsignedWord width, .unsignedWord width, .unsignedWord width,
        .bit, .bit, .unsignedWord width, .unsignedWord width, .unsignedWord width].map
          CShape.bitWidth).sum) =
      38 * width + 5 * modulus + 4 * measured + 2 * jWidth + 2 * kWidth + 13 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, CShape.bitWidth]
  omega

/-- The exact shape sum occupies its stated classical bits and no quantum systems. -/
lemma coreAllocationSpace_eq_bits {kind : ProblemKind} (N : Nat) :
    (allocationSpace N : SpacePool kind) = SpacePool.ofShape (.bits (allocationBits N)) := by
  have shapeCount (shapes : List CShape) :
      ((shapes.map (SpacePool.ofShape (kind := kind))).sum) .classicalBits =
        (shapes.map CShape.bitWidth).sum := by
    induction shapes with
    | nil => rfl
    | cons shape shapes ih => exact congrArg (fun count => shape.bitWidth + count) ih
  ext axis
  cases axis with
  | classicalBits =>
      simp only [allocationSpace, Pi.add_apply, shapeCount,
        LatticeCandidateSlotWorkspaceLayout.shapes_bitWidth_sum, SpacePool.ofShape, CShape.bitWidth]
      exact coreSpaceArithmetic (LatticeWideLllMachine.Width N) (modulusBits N)
        (measurementBits N) (BatchMachine.JWidth N) (BatchMachine.KWidth N)
  | quantumSystems dimension =>
      have shapeZero (shapes : List CShape) :
          ((shapes.map (SpacePool.ofShape (kind := .quantum))).sum) (.quantumSystems dimension) =
            0 := by
        induction shapes with
        | nil => rfl
        | cons shape shapes ih =>
            simpa only [List.map_cons, List.sum_cons, Pi.add_apply, SpacePool.ofShape,
              Nat.zero_add] using ih
      simp only [allocationSpace, Pi.add_apply, shapeZero, SpacePool.ofShape, Nat.zero_add]

/-- Number of physical cells in the three actual core packages. -/
def allocationCells (N : Nat) : Nat :=
  (LatticeCandidateSharedWorkspaceLayout.shapes N).length +
    (LatticeCandidateSlotWorkspaceLayout.shapes N).length +
    (LatticePairStateWorkspaceLayout.shapes N).length

/-- The three core lists allocate exactly 63 physical cells. -/
lemma coreAllocationCells_eq (N : Nat) : allocationCells N = 63 := rfl

private lemma threeSpace_reassociate {kind : ProblemKind}
    (first second third extra base : SpacePool kind) :
    first + (second + (third + extra)) + base = first + second + third + extra + base := by
  simp only [add_assoc]

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit model inner inner)
    (additional : SpacePool model.kind)

/-- The actual core resident peak includes all three packages and the body's extra space. -/
lemma withWorkspaces_resident_le
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).peakResidentSpace path ≤
        additional + inner.residentSpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakResidentSpace path ≤
      allocationSpace N + additional + ctx.residentSpace := by
  let slotSpace : SpacePool model.kind :=
    ((LatticeCandidateSlotWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  let stateSpace : SpacePool model.kind :=
    ((LatticePairStateWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  unfold withWorkspaces at path ⊢
  refine (withCellsFrom_resident_le _ _ _ (slotSpace + (stateSpace + additional)) ?_ path).trans ?_
  · intro sharedCtx shared sharedDistinct rootTransport sharedSeparated sharedPath
    apply withCellsFrom_resident_le _ _ _ (stateSpace + additional) ?_ sharedPath
    intro slotCtx slot slotDistinct slotTransport slotSeparated slotPath
    apply withCellsFrom_resident_le _ _ _ additional ?_ slotPath
    intro stateCtx state stateDistinct stateTransport stateSeparated statePath
    exact bodyBound _ _ _ statePath
  · exact le_of_eq (threeSpace_reassociate _ _ _ _ _)

/-- The actual core auxiliary peak includes all three packages and the body's extra space. -/
lemma withWorkspaces_auxiliary_le
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).peakAuxiliarySpace path ≤
        additional + inner.auxiliarySpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakAuxiliarySpace path ≤
      allocationSpace N + additional + ctx.auxiliarySpace := by
  let slotSpace : SpacePool model.kind :=
    ((LatticeCandidateSlotWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  let stateSpace : SpacePool model.kind :=
    ((LatticePairStateWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  unfold withWorkspaces at path ⊢
  refine (withCellsFrom_auxiliary_le _ _ _ (slotSpace + (stateSpace + additional)) ?_ path).trans ?_
  · intro sharedCtx shared sharedDistinct rootTransport sharedSeparated sharedPath
    apply withCellsFrom_auxiliary_le _ _ _ (stateSpace + additional) ?_ sharedPath
    intro slotCtx slot slotDistinct slotTransport slotSeparated slotPath
    apply withCellsFrom_auxiliary_le _ _ _ additional ?_ slotPath
    intro stateCtx state stateDistinct stateTransport stateSeparated statePath
    exact bodyBound _ _ _ statePath
  · exact le_of_eq (threeSpace_reassociate _ _ _ _ _)

/-- Both native space bounds hold on the same actual path through all three core packages. -/
lemma withWorkspaces_space_le
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).peakResidentSpace path ≤
          additional + inner.residentSpace ∧
        (body cells transport certificates).peakAuxiliarySpace path ≤
          additional + inner.auxiliarySpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakResidentSpace path ≤
        allocationSpace N + additional + ctx.residentSpace ∧
      (withWorkspaces ctx N body).peakAuxiliarySpace path ≤
        allocationSpace N + additional + ctx.auxiliarySpace := by
  exact ⟨withWorkspaces_resident_le ctx N body additional
      (fun cells transport certificates selected =>
        (bodyBound cells transport certificates selected).1)
      path,
    withWorkspaces_auxiliary_le ctx N body additional
      (fun cells transport certificates selected =>
        (bodyBound cells transport certificates selected).2)
      path⟩

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace
