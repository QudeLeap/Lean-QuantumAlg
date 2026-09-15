/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Constants
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout

/-!
# Shared candidate-data workspace layout

All original candidate slots reuse one raw zero word, one exponent bound, and the
four visible cells of the modular setup prefix.  This module maps those six
cells into one heterogeneous lexical allocation and derives the component
separation contracts from `Distinct` and `TransportSeparated`.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeCandidateSharedWorkspaceLayout

open Execution

noncomputable section

/-- Wide signed-word width used by the fixed-fuel lattice recovery. -/
abbrev Width (N : Nat) : Nat := LatticeWideLllMachine.Width N

/-- Shapes of the constants and visible modular setup outputs. -/
def shapes (N : Nat) : List CShape :=
  [.unsignedWord (Width N), .unsignedWord (Width N),
    .canonicalResidue (modulusBits N),
    .unsignedWord (modulusBits N + 1),
    .unsignedWord (modulusBits N), .unsignedWord (modulusBits N)]

/-- Heterogeneous storage for data shared by every candidate slot. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  ClassicalWorkspace.Cells ctx (shapes N)

/-- Index of the zero cell in the local workspace. -/
def zeroIndex (N : Nat) : Fin (shapes N).length :=
  ⟨0, by simp [shapes]⟩

/-- Index of the upper bound cell in the local workspace. -/
def upperBoundIndex (N : Nat) : Fin (shapes N).length :=
  ⟨1, by simp [shapes]⟩

/-- Index of the generator cell in the local workspace. -/
def generatorIndex (N : Nat) : Fin (shapes N).length :=
  ⟨2, by simp [shapes]⟩

/-- Index of the modulus cell in the local workspace. -/
def modulusIndex (N : Nat) : Fin (shapes N).length :=
  ⟨3, by simp [shapes]⟩

/-- Index of the target exponent cell in the local workspace. -/
def targetExponentIndex (N : Nat) : Fin (shapes N).length :=
  ⟨4, by simp [shapes]⟩

/-- Index of the target power cell in the local workspace. -/
def targetPowerIndex (N : Nat) : Fin (shapes N).length :=
  ⟨5, by simp [shapes]⟩

/-- Shared raw zero word. -/
def zero {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) : CWriteRef ctx (.unsignedWord (Width N)) :=
  (ClassicalWorkspace.cellAt cells (zeroIndex N)).ref

/-- Shared strict upper bound for the candidate exponent. -/
def upperBound {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) : CWriteRef ctx (.unsignedWord (Width N)) :=
  (ClassicalWorkspace.cellAt cells (upperBoundIndex N)).ref

/-- Canonical modular generator encoding. -/
def generator {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) :
    CWriteRef ctx (.canonicalResidue (modulusBits N)) :=
  (ClassicalWorkspace.cellAt cells (generatorIndex N)).ref

/-- Widened public modulus word. -/
def modulus {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) :
    CWriteRef ctx (.unsignedWord (modulusBits N + 1)) :=
  (ClassicalWorkspace.cellAt cells (modulusIndex N)).ref

/-- Fixed target exponent used to prepare the modular comparison value. -/
def targetExponent {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) : CWriteRef ctx (.unsignedWord (modulusBits N)) :=
  (ClassicalWorkspace.cellAt cells (targetExponentIndex N)).ref

/-- Shared modular target power checked by every candidate slot. -/
def targetPower {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) : CWriteRef ctx (.unsignedWord (modulusBits N)) :=
  (ClassicalWorkspace.cellAt cells (targetPowerIndex N)).ref

/-- The two initialized raw constants. -/
def constantRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) : LatticeCandidateConstants.Refs ctx (Width N) where
  zero := zero cells
  zeroRole := (ClassicalWorkspace.cellAt cells (zeroIndex N)).role
  upperBound := upperBound cells
  upperBoundRole := (ClassicalWorkspace.cellAt cells (upperBoundIndex N)).role

/-- Modular setup outputs wired to one transported sampler parameter. -/
def setupRefs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (transport : ClassicalWorkspace.Transport outer ctx)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeCandidateModularSetup.Refs ctx N where
  parameter := transport.liftInput parameter
  generator := generator cells
  generatorRole := (ClassicalWorkspace.cellAt cells (generatorIndex N)).role
  modulus := modulus cells
  modulusRole := (ClassicalWorkspace.cellAt cells (modulusIndex N)).role
  targetExponent := targetExponent cells
  targetExponentRole :=
    (ClassicalWorkspace.cellAt cells (targetExponentIndex N)).role
  targetPower := targetPower cells
  targetPowerRole :=
    (ClassicalWorkspace.cellAt cells (targetPowerIndex N)).role

/-- Index of one caller-visible mutable modular-setup cell. -/
def setupIndex (N : Nat) :
    LatticeCandidateModularSetup.MutableCell → Fin (shapes N).length
  | .generator => generatorIndex N
  | .modulus => modulusIndex N
  | .targetExponent => targetExponentIndex N
  | .targetPower => targetPowerIndex N

/-- The setup's mutable-key projection is exactly the layout projection. -/
theorem setupMutableKey {kind : ProblemKind} {outer ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (transport : ClassicalWorkspace.Transport outer ctx)
    (parameter : CInputRef outer (ParameterShape N))
    (cell : LatticeCandidateModularSetup.MutableCell) :
    LatticeCandidateModularSetup.mutableKey
        (setupRefs cells transport parameter) cell =
      (ClassicalWorkspace.cellAt cells (setupIndex N cell)).ref.toCStorageRef.key := by
  cases cell <;> rfl

/-- Layout indices of distinct setup cells are distinct. -/
private theorem setupIndex_injective (N : Nat) :
    Function.Injective (setupIndex N) := by
  intro left right equal
  cases left <;> cases right <;>
    simp [setupIndex, generatorIndex, modulusIndex, targetExponentIndex,
      targetPowerIndex] at equal ⊢

/-- Distinct layout cells supply the two-constant separation contract. -/
theorem constantSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (cells : Cells ctx N) (distinct : cells.Distinct) :
    LatticeCandidateConstants.Separation (constantRefs cells) := by
  refine ⟨?_⟩
  change (ClassicalWorkspace.cellAt cells (upperBoundIndex N)).ref.key ∉
    [(ClassicalWorkspace.cellAt cells (zeroIndex N)).ref.key]
  simp only [List.mem_singleton]
  intro equal
  have indices := ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct equal
  have values := congrArg Fin.val indices
  norm_num [upperBoundIndex, zeroIndex] at values

/-- Outer-parameter separation and cell distinctness supply modular setup. -/
theorem setupSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (distinct : cells.Distinct)
    (transport : ClassicalWorkspace.Transport outer ctx)
    (separated : cells.TransportSeparated transport)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeCandidateModularSetup.Separation
      (setupRefs cells transport parameter) := by
  refine ⟨?_, ?_⟩
  · intro cell
    rw [setupMutableKey]
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids
      cells transport separated parameter (setupIndex N cell)
  · intro left right equal
    apply setupIndex_injective N
    apply ClassicalWorkspace.workspaceCells_cellAt_key_injective cells distinct
    simpa only [setupMutableKey cells transport parameter] using equal

end

end LatticeCandidateSharedWorkspaceLayout
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
