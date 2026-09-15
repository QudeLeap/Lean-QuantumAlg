/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Space

/-!
# Actual general order-finding live space

The original borrowed base stays live alongside the sampled quantum systems,
both measured bit representations, the retained optional result and the true
recovery scratch peak. History labels contribute no physical storage.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

private def recoveryBits (t width : Nat) : Nat :=
  ClassicalRoutines.OrderRecovery.Native.extraClassicalBits width t

/-- Independent added capacity for sampling, retained option and finite recovery scratch. -/
def spaceBudget (t width : Nat) : SpacePool .quantum :=
  Sampling.spaceBudget t width + SpacePool.ofShape (.bits (t + 2 + recoveryBits t width))

private theorem final_resident_eq (t width : Nat) :
    (post t width).residentSpace + SpacePool.ofShape (.bits (recoveryBits t width)) =
      spaceBudget t width + (pre width).residentSpace := by
  rw [post, RuntimeCtx.residentSpace_addRetained]
  have sampled := Sampling.Framed.post_residentSpace (pre width) (pre_quantumWires width) t width
  change (NativeSampling.post t width).residentSpace =
    Sampling.spaceBudget t width + (pre width).residentSpace at sampled
  rw [sampled]
  ext axis
  cases axis <;> simp [spaceBudget, outputShape, SpacePool.ofShape]
  omega

private theorem final_auxiliary_eq (t width : Nat) :
    (post t width).auxiliarySpace + SpacePool.ofShape (.bits (recoveryBits t width)) =
      spaceBudget t width + (pre width).auxiliarySpace := by
  rw [post, RuntimeCtx.auxiliarySpace_addRetained]
  have sampled := Sampling.Framed.post_auxiliarySpace (pre width) (pre_quantumWires width) t width
  change (NativeSampling.post t width).auxiliarySpace =
    Sampling.spaceBudget t width + (pre width).auxiliarySpace at sampled
  rw [sampled]
  ext axis
  cases axis <;> simp [spaceBudget, outputShape, SpacePool.ofShape]
  omega

private theorem sampling_spaces (t width : Nat) :
    (NativeSampling.post t width).residentSpace ≤ spaceBudget t width + (pre width).residentSpace ∧
      (NativeSampling.post t width).auxiliarySpace ≤
        spaceBudget t width + (pre width).auxiliarySpace := by
  constructor
  · rw [← final_resident_eq, post, RuntimeCtx.residentSpace_addRetained]
    intro axis
    change (NativeSampling.post t width).residentSpace axis ≤
      (SpacePool.ofShape (outputShape t) axis +
        (NativeSampling.post t width).residentSpace axis) +
        SpacePool.ofShape (.bits (recoveryBits t width)) axis
    omega
  · rw [← final_auxiliary_eq, post, RuntimeCtx.auxiliarySpace_addRetained]
    intro axis
    change (NativeSampling.post t width).auxiliarySpace axis ≤
      (SpacePool.ofShape (outputShape t) axis +
        (NativeSampling.post t width).auxiliarySpace axis) +
        SpacePool.ofShape (.bits (recoveryBits t width)) axis
    omega

private theorem final_spaces (t width : Nat) :
    (post t width).residentSpace ≤ spaceBudget t width + (pre width).residentSpace ∧
      (post t width).auxiliarySpace ≤ spaceBudget t width + (pre width).auxiliarySpace := by
  rw [← final_resident_eq, ← final_auxiliary_eq]
  constructor <;> intro axis <;> exact Nat.le_add_right _ _

private theorem visited_spaces {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (path : (code hinput A).Path)
    (visited : RuntimeCtx .quantum)
    (present : visited ∈ (code hinput A).visitedContexts path) :
    visited.residentSpace ≤ spaceBudget t width + (pre width).residentSpace ∧
      visited.auxiliarySpace ≤ spaceBudget t width + (pre width).auxiliarySpace := by
  change visited ∈ (NativeSampling.code A).visitedContexts path.1 ++
    ([NativeSampling.post t width, post t width] ++
      (recoveryCode hinput A).visitedContexts path.2.2) at present
  rcases List.mem_append.mp present with sampled | later
  · have actual := Sampling.Framed.visited_spaces (pre width) (pre_quantumWires width)
      A path.1 visited sampled
    constructor
    · intro axis
      have bounded := actual.1 axis
      change _ ≤ (Sampling.spaceBudget t width axis + _) + _
      change _ ≤ Sampling.spaceBudget t width axis + (pre width).residentSpace axis at bounded
      omega
    · intro axis
      have bounded := actual.2 axis
      change _ ≤ (Sampling.spaceBudget t width axis + _) + _
      change _ ≤ Sampling.spaceBudget t width axis + (pre width).auxiliarySpace axis at bounded
      omega
  · rcases List.mem_append.mp later with retained | recovered
    · rcases List.mem_cons.mp retained with same | same
      · subst visited
        exact sampling_spaces t width
      · have eq := List.mem_singleton.mp same
        subst visited
        exact final_spaces t width
    · have actual :=
        ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_visited_space_le
          (recoverySpec hinput A) (baseInput t width) (sampleInput t width) (resultRef t width)
          path.2.2 visited recovered
      exact ⟨actual.1.trans_eq (final_resident_eq t width),
        actual.2.trans_eq (final_auxiliary_eq t width)⟩

/-- Actual full resident peak includes the original base and all simultaneously live storage. -/
theorem code_resident_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (path : (code hinput A).Path) :
    (code hinput A).peakResidentSpace path ≤
      spaceBudget t width + (pre width).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (visited_spaces hinput A path visited present).1

/-- Actual full auxiliary peak accounts separately for the pre-existing borrowed base. -/
theorem code_auxiliary_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (path : (code hinput A).Path) :
    (code hinput A).peakAuxiliarySpace path ≤
      spaceBudget t width + (pre width).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (visited_spaces hinput A path visited present).2

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
