/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core.Space

/-!
# Joint physical space of all six actual pair-recovery packages

All core, target, fixed-fuel LLL and nearest-plane shapes are simultaneously
live at the body. Their exact independent sum bounds the allocation overhead
on the same actual path used for the body's resident and auxiliary bounds.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace

open Execution.ClassicalWorkspace

/-- Exact simultaneous space of all six shape lists used by actual pair recovery. -/
def allocationSpace {kind : ProblemKind} (N : Nat) : SpacePool kind :=
  LatticePairCoreWorkspace.allocationSpace N +
    ((LatticeWideTargetWorkspaceLayout.shapes N).map SpacePool.ofShape).sum +
    ((LatticeFixedFuelScratchWorkspaceLayout.shapes N).map SpacePool.ofShape).sum +
    ((LatticeNearestPlaneScratchWorkspaceLayout.shapes N).map SpacePool.ofShape).sum

/-- Independent classical-bit formula for all six simultaneously live packages. -/
def allocationBits (N : Nat) : Nat :=
  104 * LatticeWideLllMachine.Width N + 5 * modulusBits N + 4 * measurementBits N +
    2 * BatchMachine.JWidth N + 2 * BatchMachine.KWidth N + 33

private theorem pairSpaceArithmetic {kind : ProblemKind}
    (width modulus measured jWidth kWidth : Nat) :
    (SpacePool.ofShape (.bits
      (38 * width + 5 * modulus + 4 * measured + 2 * jWidth + 2 * kWidth + 13)) +
    (([.unsignedWord width, .unsignedWord width,
      .unsignedWord width, .bit, .bit,
      .unsignedWord width, .bit, .bit]).map SpacePool.ofShape).sum +
    (([.unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .bit,
      .unsignedWord (width + 1), .unsignedWord (width + 1),
      .product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)),
      .unsignedWord width, .unsignedWord width, .bit,
      .unsignedWord (width + 1), .unsignedWord (width + 1),
      .product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)),
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .bit, .unsignedWord width]).map SpacePool.ofShape).sum +
    (([.unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width, .unsignedWord width, .bit,
      .unsignedWord (width + 1), .unsignedWord (width + 1),
      .product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)),
      .unsignedWord width, .unsignedWord width,
      .unsignedWord width]).map SpacePool.ofShape).sum : SpacePool kind) =
      SpacePool.ofShape (.bits
        (104 * width + 5 * modulus + 4 * measured + 2 * jWidth + 2 * kWidth + 33)) := by
  ext axis
  cases axis <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SpacePool.ofShape, Pi.add_apply, Pi.zero_apply, CShape.bitWidth] <;> omega

/-- Every actual allocated bit is counted exactly, with zero allocated quantum systems. -/
theorem pairAllocationSpace_eq_bits {kind : ProblemKind} (N : Nat) :
    (allocationSpace N : SpacePool kind) = SpacePool.ofShape (.bits (allocationBits N)) := by
  rw [allocationSpace, LatticePairCoreWorkspace.coreAllocationSpace_eq_bits]
  exact pairSpaceArithmetic (LatticeWideLllMachine.Width N) (modulusBits N)
    (measurementBits N) (BatchMachine.JWidth N) (BatchMachine.KWidth N)

/-- Number of physical cells across the six actual allocation lists. -/
def allocationCells (N : Nat) : Nat :=
  LatticePairCoreWorkspace.allocationCells N +
    (LatticeWideTargetWorkspaceLayout.shapes N).length +
    (LatticeFixedFuelScratchWorkspaceLayout.shapes N).length +
    (LatticeNearestPlaneScratchWorkspaceLayout.shapes N).length

/-- All six packages allocate exactly 134 physical cells. -/
theorem pairAllocationCells_eq (N : Nat) : allocationCells N = 134 := by
  have target : (LatticeWideTargetWorkspaceLayout.shapes N).length = 8 := rfl
  have lll : (LatticeFixedFuelScratchWorkspaceLayout.shapes N).length = 42 := rfl
  have nearest : (LatticeNearestPlaneScratchWorkspaceLayout.shapes N).length = 21 := rfl
  rw [allocationCells, LatticePairCoreWorkspace.coreAllocationCells_eq, target, lll, nearest]

private theorem fourSpace_reassociate {kind : ProblemKind}
    (first second third fourth extra base : SpacePool kind) :
    first + (second + (third + (fourth + extra))) + base =
      first + second + third + fourth + extra + base := by
  simp only [add_assoc]

variable {model : ExecutionModel} (ctx : RuntimeCtx model.kind) (N : Nat)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner), Certificates transport cells → Circuit model inner inner)
    (additional : SpacePool model.kind)

/-- The actual resident peak jointly accounts for all six packages and body allocations. -/
theorem withWorkspaces_resident_le
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).peakResidentSpace path ≤
        additional + inner.residentSpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakResidentSpace path ≤
      allocationSpace N + additional + ctx.residentSpace := by
  let targetSpace : SpacePool model.kind :=
    ((LatticeWideTargetWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  let lllSpace : SpacePool model.kind :=
    ((LatticeFixedFuelScratchWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  let nearestSpace : SpacePool model.kind :=
    ((LatticeNearestPlaneScratchWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  unfold withWorkspaces at path ⊢
  refine (LatticePairCoreWorkspace.withWorkspaces_resident_le _ _ _
    (targetSpace + (lllSpace + (nearestSpace + additional))) ?_ path).trans ?_
  · intro coreCtx core coreTransport coreCertificates corePath
    apply withCellsFrom_resident_le _ _ _ (lllSpace + (nearestSpace + additional)) ?_ corePath
    intro targetCtx target targetDistinct targetTransport targetSeparated targetPath
    apply withCellsFrom_resident_le _ _ _ (nearestSpace + additional) ?_ targetPath
    intro lllCtx lll lllDistinct lllTransport lllSeparated lllPath
    apply withCellsFrom_resident_le _ _ _ additional ?_ lllPath
    intro nearestCtx nearest nearestDistinct nearestTransport nearestSeparated nearestPath
    exact bodyBound _ _ _ nearestPath
  · exact le_of_eq (fourSpace_reassociate _ _ _ _ _ _)

/-- The actual auxiliary peak jointly accounts for all six packages and body allocations. -/
theorem withWorkspaces_auxiliary_le
    (bodyBound : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner N)
      (transport : Transport ctx inner) (certificates : Certificates transport cells)
      (path : (body cells transport certificates).Path),
      (body cells transport certificates).peakAuxiliarySpace path ≤
        additional + inner.auxiliarySpace)
    (path : (withWorkspaces ctx N body).Path) :
    (withWorkspaces ctx N body).peakAuxiliarySpace path ≤
      allocationSpace N + additional + ctx.auxiliarySpace := by
  let targetSpace : SpacePool model.kind :=
    ((LatticeWideTargetWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  let lllSpace : SpacePool model.kind :=
    ((LatticeFixedFuelScratchWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  let nearestSpace : SpacePool model.kind :=
    ((LatticeNearestPlaneScratchWorkspaceLayout.shapes N).map SpacePool.ofShape).sum
  unfold withWorkspaces at path ⊢
  refine (LatticePairCoreWorkspace.withWorkspaces_auxiliary_le _ _ _
    (targetSpace + (lllSpace + (nearestSpace + additional))) ?_ path).trans ?_
  · intro coreCtx core coreTransport coreCertificates corePath
    apply withCellsFrom_auxiliary_le _ _ _ (lllSpace + (nearestSpace + additional)) ?_ corePath
    intro targetCtx target targetDistinct targetTransport targetSeparated targetPath
    apply withCellsFrom_auxiliary_le _ _ _ (nearestSpace + additional) ?_ targetPath
    intro lllCtx lll lllDistinct lllTransport lllSeparated lllPath
    apply withCellsFrom_auxiliary_le _ _ _ additional ?_ lllPath
    intro nearestCtx nearest nearestDistinct nearestTransport nearestSeparated nearestPath
    exact bodyBound _ _ _ nearestPath
  · exact le_of_eq (fourSpace_reassociate _ _ _ _ _ _)

/-- Resident and auxiliary bounds hold jointly on one actual path through all six scopes. -/
theorem withWorkspaces_space_le
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

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace
