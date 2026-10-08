/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Depth

/-!
# Native resources of the complete retained residue sampler

The independent coordinate allowance includes the actual random-bit draw and
all deterministic preparation instructions. The two real retained allocations
have no native events. Unit-duration depth follows the chosen execution path;
the allowance also covers the unselected decision arm and has a larger card.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]

/-- Independent allowance for the actual random draw and expanded residue preparation. -/
def nativeEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (N : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation
    (BitWord.selectedCoordinate (execution := model) (.randomBits (residueSamplingBits N)))) +
    Program.nativeEnvelope model N

omit [BitWord.Selected model] in
/-- The two real retained allocations add no native operations. -/
theorem samplerRetained_allocation_trace (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (allocation (model := model)
        ctx N).Path) : (allocation (model := model) ctx N).eventTrace path = [] := rfl

/-- Every sampled body path obeys the independent coordinate-wise native allowance. -/
theorem samplerRetained_body_pool_le (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (body (model := model) ctx N).Path) :
    (body (model := model) ctx N).resourcePool path ≤ nativeEnvelope model N := by
  change ResourcePool.ofList ((PackedSample.draw (model := model)
      N (sampleRef ctx N)).eventTrace path.1 ++
    (Program.circuit (model := model) N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N)).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (PackedSample.packedSample_draw_pool (model := model)
      N (sampleRef ctx N) path.1).le
    (Program.samplerProgram_pool_le (model := model) N (FirstAccepted.cellRead (sampleRef ctx N))
      (parameterRef ctx N) path.2)

/-- The full circuit charges the sampled native path after its two real allocations. -/
theorem samplerRetained_pool_le (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (circuit (model := model) ctx N).Path) :
    (circuit (model := model) ctx N).resourcePool path ≤ nativeEnvelope model N := by
  change ResourcePool.ofList ((allocation (model := model) ctx N).eventTrace path.1 ++
    (body (model := model) ctx N).eventTrace path.2) ≤ _
  rw [samplerRetained_allocation_trace, List.nil_append]
  exact samplerRetained_body_pool_le (model := model) ctx N path.2

/-- Exact capacity of the independent native allowance, including the random draw. -/
theorem samplerRetainedEnvelope_card (model : ExecutionModel) [BitWord.Selected model] (N : Nat) :
    (nativeEnvelope model N).card = 44 * modulusBits N + 163 := by
  simp only [nativeEnvelope, Multiset.card_add, ResourcePool.singleton,
    Multiset.card_replicate, Program.samplerProgramEnvelope_card]
  omega

/-- The actual sampled body has one random layer followed by its selected preparation path. -/
theorem samplerRetained_body_unit_depth_le (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (body (model := model) ctx N).Path) :
    (body (model := model) ctx N).depth (fun _ => 1) path ≤ 44 * modulusBits N + 161 := by
  have prepared := Program.samplerProgram_unit_depth_le (model := model) N
    (FirstAccepted.cellRead (sampleRef ctx N)) (parameterRef ctx N) path.2
  change (PackedSample.draw (model := model) N (sampleRef ctx N)).depth (fun _ => 1) path.1 +
    (Program.circuit (model := model) N (FirstAccepted.cellRead (sampleRef ctx N))
    (parameterRef ctx N)).depth (fun _ => 1) path.2 ≤ _
  rw [PackedSample.packedSample_draw_unit_depth]
  omega

/-- Real retention contributes no event duration to the complete sampler's chosen path. -/
theorem samplerRetained_unit_depth_le (ctx : RuntimeCtx model.kind) (N : Nat)
    (path : (circuit (model := model) ctx N).Path) :
    (circuit (model := model) ctx N).depth (fun _ => 1) path ≤ 44 * modulusBits N + 161 := by
  change (0 + 0) + (body (model := model) ctx N).depth (fun _ => 1) path.2 ≤ _
  simpa only [Nat.zero_add] using samplerRetained_body_unit_depth_le (model := model) ctx N path.2

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
