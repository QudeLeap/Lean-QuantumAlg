/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Workspace.Separation

/-!
# Physical wide-target separation inside pair recovery

The persistent pair-state package supplies every source read of the target
loader, while the dedicated eight-cell package supplies every mutable target
scratch cell.  Their allocation certificates therefore discharge the compact
wide-target frame contract.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairWideTargetWorkspaceSeparation

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

private theorem storageRead_not_mem {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} {source : CStorageRef ctx shape} {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (CInputRef.storage source).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton, ne_comm] using different

/-- The state-to-target cross certificate gives every source-to-scratch
avoidance required by the wide target loader. -/
theorem externalAvoids {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal : CInputRef ctx (.bits (measurementBits N))) :
    LatticeWideTargetWorkspaceSeparation.ExternalAvoids cells.target
      (LatticeWideTargetWorkspaceViews.targetRefs cells.core.state cells.target
        (LatticePairStateWorkspaceViews.pairRefs cells.core.state
          firstTerminal secondTerminal)) := by
  intro source target
  let cross := certificates.coreTarget.state
  cases source with
  | firstK =>
      apply storageRead_not_mem
      exact cross.keysNe
        (LatticePairStateWorkspaceLayout.cellIndex N .firstK)
        (LatticeWideTargetWorkspaceLayout.cellIndex N target)
  | secondK =>
      apply storageRead_not_mem
      exact cross.keysNe
        (LatticePairStateWorkspaceLayout.cellIndex N .secondK)
        (LatticeWideTargetWorkspaceLayout.cellIndex N target)
  | modulus =>
      apply storageRead_not_mem
      exact cross.keysNe
        (LatticePairStateWorkspaceLayout.cellIndex N .basis21)
        (LatticeWideTargetWorkspaceLayout.cellIndex N target)
  | firstOutput =>
      apply storageRead_not_mem
      exact cross.keysNe
        (LatticePairStateWorkspaceLayout.cellIndex N .targetFirst)
        (LatticeWideTargetWorkspaceLayout.cellIndex N target)
  | secondOutput =>
      apply storageRead_not_mem
      exact cross.keysNe
        (LatticePairStateWorkspaceLayout.cellIndex N .targetSecond)
        (LatticeWideTargetWorkspaceLayout.cellIndex N target)
  | third =>
      apply storageRead_not_mem
      exact cross.keysNe
        (LatticePairStateWorkspaceLayout.cellIndex N .targetThird)
        (LatticeWideTargetWorkspaceLayout.cellIndex N target)

/-- The physical state and target packages supply the compact frame
separation expected by `LatticeWideTargetWorkspaceSeparation`. -/
theorem frameSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal : CInputRef ctx (.bits (measurementBits N))) :
    LatticeWideTargetWorkspaceSeparation.FrameSeparation
      (LatticeWideTargetWorkspaceViews.targetRefs cells.core.state cells.target
        (LatticePairStateWorkspaceViews.pairRefs cells.core.state
          firstTerminal secondTerminal)) :=
  LatticeWideTargetWorkspaceSeparation.frameSeparation cells.core.state
    certificates.core.stateDistinct cells.target certificates.targetDistinct
      (LatticePairStateWorkspaceViews.pairRefs cells.core.state
        firstTerminal secondTerminal)
      (externalAvoids certificates firstTerminal secondTerminal)

/-- The complete semantic target-loader separation follows from the same
physical certificate. -/
theorem targetSeparation {kind : ProblemKind}
    {outer ctx : RuntimeCtx kind} {N : Nat}
    {transport : Transport outer ctx}
    {cells : LatticePairRecoveryWorkspace.Cells ctx N}
    (certificates : LatticePairRecoveryWorkspace.Certificates transport cells)
    (firstTerminal secondTerminal : CInputRef ctx (.bits (measurementBits N))) :
    LatticeWideTargetMachine.Separation
      (LatticeWideTargetWorkspaceViews.targetRefs cells.core.state cells.target
        (LatticePairStateWorkspaceViews.pairRefs cells.core.state
          firstTerminal secondTerminal)) :=
  LatticeWideTargetWorkspaceSeparation.targetSeparation _
    (frameSeparation certificates firstTerminal secondTerminal)

end

end LatticePairWideTargetWorkspaceSeparation
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
