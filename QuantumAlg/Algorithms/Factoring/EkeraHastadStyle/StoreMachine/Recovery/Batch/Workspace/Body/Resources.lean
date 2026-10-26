/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Endpoint

/-!
# Independent native and storage bounds of the actual allocated body

The shared prefix and seeded batch endpoint contribute their actual native
paths in order. Both include the same complete entry context and reusable
native-power scratch allowance in resident and auxiliary storage.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody

open Execution
open ClassicalRoutines

noncomputable section

variable {additionalMembers : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {root topCtx inner : RuntimeCtx model.kind} {N : Nat}

/-- Independent native budgets of initialization and the complete seeded batch endpoint. -/
def eventEnvelope (N : Nat) (additionalMembers : Nat := 14) : ResourcePool model :=
  LatticeSharedQuadraticInitialization.eventEnvelope N +
    LatticeBatchRecoveryEndpoint.eventEnvelope N additionalMembers

/-- Independent chronological dependency depth of both complete phases. -/
def depthBound (N : Nat) (additionalMembers : Nat := 14) : Nat :=
  LatticeSharedQuadraticInitialization.depthBound N + LatticeBatchRecoveryEndpoint.depthBound N
    additionalMembers

omit [BitWord.Selected model] in
private lemma sequence_pool_le (first second : Circuit model inner inner)
    (firstBound secondBound : ResourcePool model)
    (firstLe : ∀ path, first.resourcePool path ≤ firstBound)
    (secondLe : ∀ path, second.resourcePool path ≤ secondBound)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path ≤ firstBound + secondBound := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (firstLe path.1) (secondLe path.2)

/-- Every possible actual native path satisfies both independent component allowances. -/
lemma into_pool_le (input : Input N) (refs : Refs root topCtx inner N additionalMembers)
    (path : (into input refs).Path) :
    (into input refs).resourcePool path ≤ eventEnvelope N additionalMembers := by
  unfold into at path ⊢
  unfold eventEnvelope
  with_reducible
    exact sequence_pool_le _ _ _ _
      (LatticeSharedQuadraticInitialization.into_pool_le input (initializationRefs refs))
      (LatticeBatchRecoveryEndpoint.into_pool_le input (endpointRefs refs)) path

/-- The complete actual path runs initialization before the complete recovery endpoint. -/
lemma into_depth_le (input : Input N) (refs : Refs root topCtx inner N additionalMembers)
    (path : (into input refs).Path) :
    (into input refs).depth (fun _ => 1) path ≤ depthBound N additionalMembers :=
  Nat.add_le_add
    (LatticeSharedQuadraticInitialization.into_depth_le input (initializationRefs refs) path.1)
    (LatticeBatchRecoveryEndpoint.into_depth_le input (endpointRefs refs) path.2)

/-- Resident storage includes the actual context and temporary native powering allocation. -/
lemma into_resident_le (input : Input N) (refs : Refs root topCtx inner N additionalMembers)
    (path : (into input refs).Path) :
    (into input refs).peakResidentSpace path ≤
      inner.residentSpace + Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans ?_
  exact SpacePool.max_le
    (LatticeSharedQuadraticInitialization.into_resident_le input (initializationRefs refs) path.1)
    (LatticeBatchRecoveryEndpoint.into_resident_le input (endpointRefs refs) path.2)

/-- Auxiliary storage includes the existing roles and every native-power temporary. -/
lemma into_auxiliary_le (input : Input N) (refs : Refs root topCtx inner N additionalMembers)
    (path : (into input refs).Path) :
    (into input refs).peakAuxiliarySpace path ≤
      inner.auxiliarySpace + Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans ?_
  exact SpacePool.max_le
    (LatticeSharedQuadraticInitialization.into_auxiliary_le input (initializationRefs refs) path.1)
    (LatticeBatchRecoveryEndpoint.into_auxiliary_le input (endpointRefs refs) path.2)

/-- Joint borrowed-reference restoration composes over both actual phases. -/
lemma into_borrowedRestored (input : Input N) (refs : Refs root topCtx inner N additionalMembers)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State inner Reference (model.HiddenState × History)) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (LatticeSharedQuadraticInitialization.into_borrowedRestored input (initializationRefs refs)
      Reference state)
    (LatticeBatchRecoveryEndpoint.into_borrowedRestored input (endpointRefs refs) Reference _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody
