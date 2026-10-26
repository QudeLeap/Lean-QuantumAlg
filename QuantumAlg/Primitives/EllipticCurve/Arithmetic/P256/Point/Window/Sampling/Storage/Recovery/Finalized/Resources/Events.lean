/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Resources.Events
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Resources.Events
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting.Events

/-!
# Complete independent events of the actual finalized three-attempt run

The finite allowance includes the original whole-bank restart, literal
34-window sampler, paid nearest recovery, final whole-bank cleanup and
native optional-result packing. Its labels and multiplicities depend only
on public arithmetic parameters, independently of stores, paths and runs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage.Inputs

noncomputable section

open Execution ClassicalWorkspace ClassicalRoutines.EllipticCurve
open ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

/-- Independent complete native allowance for one actual restart, sample and paid check. -/
def attemptEventEnvelope (services : ClassicalOracleModel) (spec : ModulusSpec 256)
    (curve : CurveSpec 256) (order : ModulusSpec 260) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  Initialization.eventEnvelope services + Sampling.eventEnvelope services spec +
    CandidateCheck.Native.Nearest.attemptEnvelope
      (.quantum AlgorithmGate.model .empty BitWord.model services) curve order

/-- All three paid attempts, terminal cleanup and the original native option pack. -/
def finalizedEventEnvelope (services : ClassicalOracleModel) (spec : ModulusSpec 256)
    (curve : CurveSpec 256) (order : ModulusSpec 260) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  (3 • attemptEventEnvelope services spec curve order +
    ResourcePool.scale 854 (Cleanup.Parameters.oneBudget (services := services))) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.classicalOperation (.nominalEncoding (.packOption 260))) 1

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)

attribute [local irreducible] Circuit.resourcePool ResourcePool.scale
  Initialization.program Initialization.placedProgram scopedAttemptsFinalized withFrame

private lemma restart_events (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    (original.restart (services := services) output).resourcePool path ≤
      Initialization.eventEnvelope services := by
  unfold restart at path ⊢
  refine (Circuit.resourcePool_embed
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (allowAllocation := true)
    (ContextEmbedding.identity ctx) _ path).le.trans ?_
  exact Initialization.prepared_pool_le _ _ _ path

/-- Every actual attempt pays both quantum stages and all native recovery instructions. -/
lemma attempt_pool_le (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    (original.attempt (services := services) sampler checkers).resourcePool path ≤
      attemptEventEnvelope services sampler.modulus original.curve original.order := by
  unfold attempt at path ⊢
  have reset := original.restart_events (sampler.output 0) path.1.1
  have sample := sampler.circuit_pool_le path.1.2
  have recovery := CandidateCheck.Native.Nearest.attemptInto_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (ctx := ctx)
    original.curve original.order (Recovery.pairedInput sampler) original.base original.target
    checkers.inverseSuccess checkers.candidate checkers.reconstruction checkers.scalarResult
    checkers.targetAccepted checkers.accepted checkers.selected path.2
  rw [WindowTables.Accounting.seq_pool, WindowTables.Accounting.seq_pool]
  unfold attemptEventEnvelope
  exact add_le_add (add_le_add reset sample) recovery

private lemma finalizedInnerBody_pool_le {inner : RuntimeCtx .quantum} (inputs : Inputs inner)
    (sampler : Sampling.Parameters inner) (checkers : Checkers inner) (count : Nat)
    (path : (inputs.finalizedInnerBody (services := services) sampler checkers count).Path) :
    (inputs.finalizedInnerBody (services := services) sampler checkers count).resourcePool path ≤
      count • attemptEventEnvelope services sampler.modulus inputs.curve inputs.order +
        ResourcePool.scale 854 (Cleanup.Parameters.oneBudget (services := services)) := by
  unfold finalizedInnerBody at path ⊢
  let cleanup := finalizedCleanup sampler
  have attempts := WindowTables.Accounting.range_pool_le count
    (fun _ => inputs.attempt (services := services) sampler checkers)
    (attemptEventEnvelope services sampler.modulus inputs.curve inputs.order)
    (fun _ selected => inputs.attempt_pool_le sampler checkers selected) path.1
  have terminal := cleanup.circuit_pool_le (services := services) path.2
  rw [WindowTables.Accounting.seq_pool, Circuit.resourcePool_embed]
  exact add_le_add attempts terminal

private lemma scopedAttemptsFinalized_pool_le (count : Nat)
    (path : (original.scopedAttemptsFinalized (services := services) count).Path) :
    (original.scopedAttemptsFinalized (services := services) count).resourcePool path ≤
      count • attemptEventEnvelope services original.modulus original.curve original.order +
        ResourcePool.scale 854 (Cleanup.Parameters.oneBudget (services := services)) := by
  apply ResourcePool.le_iff_count.mpr
  intro event
  unfold scopedAttemptsFinalized at path ⊢
  apply withFrame_count_le (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ 256 256 _ event _ ?_ path
  intro inner lift same frame fresh selected
  let retained := original.transport (Recovery.persistentTransport ctx)
    (Recovery.persistent_wires ctx)
  let sampler := retained.samplerParameters lift same frame fresh
  let inputs := retained.transport lift same
  let checkers := (Checkers.retained ctx).transport lift
  exact ResourcePool.le_iff_count.mp
    (finalizedInnerBody_pool_le inputs sampler checkers count selected) event

/-- The sole complete finalized run is bounded in every declaration-owned event coordinate. -/
lemma runFinalized_pool_le
    (path : (original.runFinalized (services := services)).code.Path) :
    (original.runFinalized (services := services)).code.resourcePool path ≤
      finalizedEventEnvelope services original.modulus original.curve original.order := by
  unfold runFinalized at path ⊢
  have attempts := original.scopedAttemptsFinalized_pool_le (services := services) 3 path.1.2
  have packed := CandidateCheck.Native.packBatchResult_resourcePool
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260 path.2
  rw [WindowTables.Accounting.seq_pool, WindowTables.Accounting.seq_pool,
    CandidateCheck.Native.retainPersistent_resourcePool, zero_add, packed]
  unfold finalizedEventEnvelope
  exact add_le_add attempts le_rfl

end
end Storage.Inputs
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
