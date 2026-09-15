/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Shared.Workspace.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources

/-!
# Physical shared and quadratic workspace prefix

The six shared modular cells are allocated first and transported through the
twenty-six-cell quadratic package.  The deepest callback receives both live
packages and the complete separation certificate for their literal
initialization routine.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeSharedQuadraticWorkspace

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

namespace Shared

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeCandidateSharedWorkspaceLayout.Cells ctx N

end Shared

namespace Quadratic

/-- Abbreviation for the local cell interface. -/
abbrev Cell := QuadraticScratchLayout.Cell

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  QuadraticScratchLayout.Cells ctx N

end Quadratic

/-- The exact initialization view in one final lexical scope. -/
def refs {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (shared : Shared.Cells ctx N) (quadratic : Quadratic.Cells ctx N)
    (transport : Transport outer ctx)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeSharedQuadraticInitialization.Refs ctx N where
  setup := LatticeCandidateSharedWorkspaceLayout.setupRefs
    shared transport parameter
  quadratic := quadratic

/-- The initializer reads the physical shared modulus cell. -/
theorem modulusSource_eq {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (shared : Shared.Cells ctx N) (quadratic : Quadratic.Cells ctx N)
    (transport : Transport outer ctx)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeSharedQuadraticInitialization.modulusSource
        (refs shared quadratic transport parameter) =
      FirstAccepted.cellRead (ClassicalWorkspace.cellAt shared
        (LatticeCandidateSharedWorkspaceLayout.modulusIndex N)).ref := by
  rfl

/-- The physical layout facts imply the complete shared-prefix separation. -/
theorem separation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    (shared : Shared.Cells ctx N) (sharedDistinct : shared.Distinct)
    (quadratic : Quadratic.Cells ctx N)
    (quadraticDistinct : quadratic.Distinct)
    (transport : Transport outer ctx)
    (sharedSeparated : shared.TransportSeparated transport)
    (quadraticSeparated : quadratic.TransportSeparated transport)
    (cross : CrossSeparated shared quadratic)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeSharedQuadraticInitialization.Separation
      (refs shared quadratic transport parameter) := by
  let initializationRefs := refs shared quadratic transport parameter
  have parameterAvoids (cell : Quadratic.Cell) :
      (QuadraticScratchLayout.cellRef quadratic cell).key ∉
        initializationRefs.setup.parameter.storageKeys := by
    exact ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids quadratic transport
      quadraticSeparated parameter (QuadraticScratchLayout.cellIndex N cell)
  have baseAvoids (cell : Quadratic.Cell) :
      (QuadraticScratchLayout.cellRef quadratic cell).key ∉
        (LatticeCandidateModularSetup.parameterBaseInput initializationRefs.setup).storageKeys :=
    parameterAvoids cell
  have sharedAvoids (index : Fin (LatticeCandidateSharedWorkspaceLayout.shapes N).length)
      (cell : Quadratic.Cell) :
      (QuadraticScratchLayout.cellRef quadratic cell).key ∉
        (FirstAccepted.cellRead (ClassicalWorkspace.cellAt shared index).ref).storageKeys := by
    have distinct := cross.keysNe index (QuadraticScratchLayout.cellIndex N cell)
    simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton,
      QuadraticScratchLayout.cellRef_key, ne_comm] using distinct
  have sourceAvoids (cell : Quadratic.Cell) :
      (QuadraticScratchLayout.cellRef quadratic cell).key ∉
        (LatticeSharedQuadraticInitialization.modulusSource initializationRefs).storageKeys :=
    sharedAvoids (LatticeCandidateSharedWorkspaceLayout.modulusIndex N) cell
  refine
    { setup := LatticeCandidateSharedWorkspaceLayout.setupSeparation shared
        sharedDistinct transport sharedSeparated parameter
      quadratic := QuadraticScratchInitialization.separation
        (LatticeSharedQuadraticInitialization.modulusSource initializationRefs)
        quadratic quadraticDistinct sourceAvoids
      parameterQuadratic := ⟨parameterAvoids .modulus,
        parameterAvoids .one, parameterAvoids .zero⟩
      baseQuadratic := ⟨baseAvoids .modulus, baseAvoids .one, baseAvoids .zero⟩
      generatorQuadratic := ⟨sharedAvoids _ .modulus, sharedAvoids _ .one, sharedAvoids _ .zero⟩
      exponentQuadratic := ⟨sharedAvoids _ .modulus, sharedAvoids _ .one, sharedAvoids _ .zero⟩
      targetPowerQuadratic := ⟨sharedAvoids _ .modulus, sharedAvoids _ .one,
        sharedAvoids _ .zero⟩ }

/-- Allocate the shared and quadratic packages and expose their complete
physical initialization interface in the deepest scope. -/
def withWorkspaces {kind : ProblemKind} (ctx : RuntimeCtx kind) {N : Nat}
    (parameter : CInputRef ctx (ParameterShape N))
    (body : ∀ {inner : RuntimeCtx kind}
      (shared : Shared.Cells inner N), shared.Distinct →
      (quadratic : Quadratic.Cells inner N) → quadratic.Distinct →
      (transport : Transport ctx inner) →
      shared.TransportSeparated transport →
      quadratic.TransportSeparated transport →
      (cross : CrossSeparated shared quadratic) →
      LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter) →
      Circuit inner inner) : Circuit ctx ctx :=
  withCells ctx
      (LatticeCandidateSharedWorkspaceLayout.shapes N) fun
      shared sharedDistinct sharedTransport sharedSeparated =>
    withCells _
        (QuadraticScratchLayout.shapes N) fun quadratic quadraticDistinct
          innerTransport quadraticInnerSeparated =>
      let sharedAt := transportCells innerTransport shared
      have sharedAtDistinct := workspaceCells_transportCells_distinct
        innerTransport shared sharedDistinct
      let combinedTransport :=
        Transport.compose sharedTransport innerTransport
      have sharedAtSeparated :=
        workspaceCells_transportCells_transportSeparated
          sharedTransport innerTransport shared sharedSeparated
      have quadraticOuterSeparated :=
        workspaceCells_transportSeparated_compose
          sharedTransport innerTransport quadratic quadraticInnerSeparated
      have cross := crossSeparated_of_nested innerTransport shared quadratic
        quadraticInnerSeparated
      body sharedAt sharedAtDistinct quadratic quadraticDistinct combinedTransport
        sharedAtSeparated quadraticOuterSeparated cross
          (separation sharedAt sharedAtDistinct quadratic quadraticDistinct
            combinedTransport sharedAtSeparated quadraticOuterSeparated cross
              parameter)

variable {kind : ProblemKind} (ctx : RuntimeCtx kind) {N : Nat}
    (parameter : CInputRef ctx (ParameterShape N))
    (body : ∀ {inner : RuntimeCtx kind}
      (shared : Shared.Cells inner N), shared.Distinct →
      (quadratic : Quadratic.Cells inner N) → quadratic.Distinct →
      (transport : Transport ctx inner) → shared.TransportSeparated transport →
      quadratic.TransportSeparated transport → (cross : CrossSeparated shared quadratic) →
      LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter) → Circuit inner inner)

/-- Actual allocation preserves a uniform native bound for every physical callback scope. -/
theorem withWorkspaces_pool_le (budget : ResourcePool kind)
    (bodyBound : ∀ {inner : RuntimeCtx kind}
      (shared : Shared.Cells inner N) (sharedDistinct : shared.Distinct)
      (quadratic : Quadratic.Cells inner N) (quadraticDistinct : quadratic.Distinct)
      (transport : Transport ctx inner) (sharedSeparated : shared.TransportSeparated transport)
      (quadraticSeparated : quadratic.TransportSeparated transport)
      (cross : CrossSeparated shared quadratic)
      (initialization : LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter))
      (path : (body shared sharedDistinct quadratic quadraticDistinct transport
          sharedSeparated quadraticSeparated cross initialization).Path),
      (body shared sharedDistinct quadratic quadraticDistinct transport
          sharedSeparated quadraticSeparated cross initialization).resourcePool path ≤ budget)
    (path : (withWorkspaces ctx parameter body).Path) :
    (withWorkspaces ctx parameter body).resourcePool path ≤ budget := by
  unfold withWorkspaces at path ⊢
  apply withCellsFrom_pool_le _ _ _ budget _ path
  intro sharedCtx shared sharedDistinct rootTransport sharedSeparated selected
  apply withCellsFrom_pool_le _ _ _ budget _ selected
  intro inner quadratic quadraticDistinct innerTransport quadraticSeparated chosen
  exact bodyBound _ _ _ _ _ _ _ _ _ chosen

/-- Lexical allocation preserves the complete actual callback dependency depth. -/
theorem withWorkspaces_depth_le (duration : Resource.Event kind → Nat) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx kind}
      (shared : Shared.Cells inner N) (sharedDistinct : shared.Distinct)
      (quadratic : Quadratic.Cells inner N) (quadraticDistinct : quadratic.Distinct)
      (transport : Transport ctx inner) (sharedSeparated : shared.TransportSeparated transport)
      (quadraticSeparated : quadratic.TransportSeparated transport)
      (cross : CrossSeparated shared quadratic)
      (initialization : LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter))
      (path : (body shared sharedDistinct quadratic quadraticDistinct transport
          sharedSeparated quadraticSeparated cross initialization).Path),
      (body shared sharedDistinct quadratic quadraticDistinct transport
          sharedSeparated quadraticSeparated cross initialization).depth duration path ≤ budget)
    (path : (withWorkspaces ctx parameter body).Path) :
    (withWorkspaces ctx parameter body).depth duration path ≤ budget := by
  unfold withWorkspaces at path ⊢
  apply withCellsFrom_depth_le _ _ _ duration budget _ path
  intro sharedCtx shared sharedDistinct rootTransport sharedSeparated selected
  apply withCellsFrom_depth_le _ _ _ duration budget _ selected
  intro inner quadratic quadraticDistinct innerTransport quadraticSeparated chosen
  exact bodyBound _ _ _ _ _ _ _ _ _ chosen

/-- Both actual allocation boundaries preserve full borrowed-reference restoration of the body. -/
theorem withWorkspaces_borrowedRestored (Reference : Register)
    (bodyRestores : ∀ {inner : RuntimeCtx kind}
      (shared : Shared.Cells inner N) (sharedDistinct : shared.Distinct)
      (quadratic : Quadratic.Cells inner N) (quadraticDistinct : quadratic.Distinct)
      (transport : Transport ctx inner) (sharedSeparated : shared.TransportSeparated transport)
      (quadraticSeparated : quadratic.TransportSeparated transport)
      (cross : CrossSeparated shared quadratic)
      (initialization : LatticeSharedQuadraticInitialization.Separation
        (refs shared quadratic transport parameter))
      {History : Type} [Fintype History] (state : State inner Reference History),
      (body shared sharedDistinct quadratic quadraticDistinct transport
          sharedSeparated quadraticSeparated cross initialization).BorrowedRestored Reference state
        ((body shared sharedDistinct quadratic quadraticDistinct transport
          sharedSeparated quadraticSeparated cross initialization).execute Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (withWorkspaces ctx parameter body).BorrowedRestored Reference state
      ((withWorkspaces ctx parameter body).execute Reference state) := by
  unfold withWorkspaces
  apply withCellsFrom_borrowedRestored
  intro sharedCtx shared sharedDistinct rootTransport sharedSeparated History _ state
  apply withCellsFrom_borrowedRestored
  intro inner quadratic quadraticDistinct innerTransport quadraticSeparated Past _ current
  exact bodyRestores _ _ _ _ _ _ _ _ _ current

end

end LatticeSharedQuadraticWorkspace
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
