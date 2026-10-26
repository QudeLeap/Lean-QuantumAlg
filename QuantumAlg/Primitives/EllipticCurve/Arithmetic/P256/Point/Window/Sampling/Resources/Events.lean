/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Resources.Bounds
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Resources.Events

/-!
# Independent complete event pools for the literal chronological sampler

Active reset, source H, the complete constructed-table point operation and
actual stored-feedback Fourier readout retain their original order and full
native event labels. The 34-window allowance is the finite sum over the
fixed public schedule, independent of incoming state and every actual path.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

open ClassicalAlgorithms.Modular

noncomputable section

/-- The complete original four-component native allowance for one public window index. -/
def blockEventEnvelope (services : ClassicalOracleModel) (spec : ModulusSpec 256)
    (index : WindowIndex) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  let single := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate .singleQubit)
  let measure := ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
  let active := index.lowerWidth + 1
  active • Cleanup.Parameters.oneBudget (services := services) +
    (active • single + (Driver.eventEnvelope services spec index.highRemaining index.lowWidth +
      ((active * index.start + active.choose 2 + 2 * active) • single + active • measure)))

/-- Independent complete finite allowance for the original public 34-window schedule. -/
def eventEnvelope (services : ClassicalOracleModel) (spec : ModulusSpec 256) :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  (schedule.map (blockEventEnvelope services spec)).sum

namespace Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Parameters ctx)

/-- All four real blocks fit their independent finite native allowances on the same path. -/
lemma block_pool_le (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (parameters.block index).resourcePool path ≤
      blockEventEnvelope services parameters.modulus index := by
  have reset := parameters.reset_pool_le index path.1
  have point := (parameters.pointParameters index).circuit_pool_le parameters.frame
    parameters.modulus index.row (parameters.pointPath index path)
  have fourier := QuantumFourierTransform.Semiclassical.Window.inverseCode_pool_le
    (operations := BitWord.model) (services := services) (parameters.ports index)
    (parameters.fourierPath index path)
  rw [QuantumFourierTransform.Semiclassical.Window.priorPhaseCount_complete] at fourier
  rw [parameters.block_resourcePool]
  exact add_le_add reset (add_le_add le_rfl (add_le_add point fourier))

/-- The original recursive sequence sums the complete native pool of every real block. -/
lemma sequence_pool_le (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    (parameters.sequence indices).resourcePool path ≤
      (indices.map (blockEventEnvelope services parameters.modulus)).sum := by
  induction indices with
  | nil => exact le_rfl
  | cons index rest ih =>
      dsimp only [sequence, Circuit.Path] at path
      have first := parameters.block_pool_le index path.1
      have tail := ih path.2
      change ResourcePool.ofList (_ ++ _) ≤ _
      rw [ResourcePool.ofList_append, List.map_cons, List.sum_cons]
      exact add_le_add first tail

/-- Every complete actual 34-window path satisfies the independent full native event budget. -/
lemma circuit_pool_le (path : (circuit (services := services) parameters).Path) :
    (circuit parameters).resourcePool path ≤ eventEnvelope services parameters.modulus :=
  parameters.sequence_pool_le schedule path

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
