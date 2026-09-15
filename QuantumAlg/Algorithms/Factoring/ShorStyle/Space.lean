/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Space
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Independent full native Shor space, including the complete recovery tail

The one physical bank uses exactly four modulus-width words. Every sampling
round retains `22m+1` actual classical bits. The final option result and all
simultaneous first-success, factor, order-recovery and arithmetic scratch fit
another `39m+26` bits. This dominates the actual sampling peak as well, including
zero rounds. The same bound applies to both resident and auxiliary space because
the sole supplied borrowed anchor has zero width. Every actual entry and release
is included by the circuit's visited-context trace.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

noncomputable section

/-- Full independent capacity in every native dimension coordinate, with no circuit argument. -/
def spaceBudget (N count : Nat) : SpacePool .quantum
  | .classicalBits => count * (22 * modulusBits N + 1) + 39 * modulusBits N + 26
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 4 * modulusBits N else 0

private def bankSpace (N : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then 4 * modulusBits N else 0

private theorem batch_allowance (N count : Nat) :
    NativeBatch.additionalBits N count ≤
      count * (22 * modulusBits N + 1) + 39 * modulusBits N + 26 := by
  cases count with
  | zero => simp [NativeBatch.additionalBits]
  | succ count =>
      simp only [NativeBatch.additionalBits, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
        Nat.add_mul, Nat.one_mul]
      omega

private theorem pre_resident : pre.residentSpace = 0 := by
  apply SpacePool.ext
  intro axis
  cases axis <;> rfl

private theorem bank_resident (N : Nat) :
    (NativeBank.context pre pre_quantumWires N).residentSpace = bankSpace N := by
  rw [NativeBank.resident, pre_resident, add_zero]
  apply SpacePool.ext
  intro axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact NativeQuantum.runtimeLayout_dimensionCount N dimension

private theorem sampled_resident (N count : Nat) :
    (sampledContext N count).residentSpace =
      bankSpace N + SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1))) := by
  change (NativePreparedBatch.context pre pre_quantumWires N count).residentSpace = _
  rw [NativePreparedBatch.context_resident, bank_resident]

private theorem sampled_resident_capacity (N count : Nat) :
    (sampledContext N count).residentSpace ≤ spaceBudget N count := by
  rw [sampled_resident]
  intro axis
  cases axis <;> simp [bankSpace, SpacePool.ofShape, spaceBudget]
  omega

private theorem post_resident (N count : Nat) :
    (post N count).residentSpace = SpacePool.ofShape (outputShape N) +
      (bankSpace N + SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1)))) := by
  rw [post, RuntimeCtx.residentSpace_addRetained, sampled_resident]

private theorem post_resident_capacity (N count : Nat) :
    (post N count).residentSpace + NativeFactorScan.Scope.spaceBound .quantum N ≤
      spaceBudget N count := by
  rw [post_resident, NativeFactorScan.Scope.spaceBound_eq]
  intro axis
  cases axis <;> simp [outputShape, bankSpace, SpacePool.ofShape, spaceBudget]
  omega

private theorem sampling_resident_le (N count : Nat)
    (path : (NativePreparedBatch.code pre pre_quantumWires N count).Path) :
    (NativePreparedBatch.code pre pre_quantumWires N count).peakResidentSpace path ≤
      spaceBudget N count := by
  have actual := NativePreparedBatch.resident_le pre pre_quantumWires N count path
  rw [bank_resident] at actual
  refine actual.trans ?_
  intro axis
  cases axis with
  | classicalBits => exact (Nat.zero_add _).le.trans (batch_allowance N count)
  | quantumSystems dimension => exact le_rfl

private theorem retain_resident_le (N count : Nat)
    (path : (Circuit.retain (sampledContext N count) (resultKey N count)
      (outputShape N) (resultFresh N count)).Path) :
    (Circuit.retain (sampledContext N count) (resultKey N count)
      (outputShape N) (resultFresh N count)).peakResidentSpace path ≤ spaceBudget N count := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  have location : visited = sampledContext N count ∨ visited = post N count := by
    change visited ∈ [sampledContext N count, post N count] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
  rcases location with old | retained
  · subst visited
    exact sampled_resident_capacity N count
  · subst visited
    exact (show (post N count).residentSpace ≤
      (post N count).residentSpace + NativeFactorScan.Scope.spaceBound .quantum N from
        fun _ => Nat.le_add_right _ _).trans (post_resident_capacity N count)

private theorem recovery_resident_le {N : Nat} (source : Input N) (count : Nat)
    (path : (recoveryStage source count).Path) :
    (recoveryStage source count).peakResidentSpace path ≤ spaceBudget N count := by
  refine (Circuit.peakResidentSpace_seq
    (.retain (sampledContext N count) (resultKey N count) (outputShape N) (resultFresh N count))
    (recoveryCode source count) path).le.trans ?_
  exact SpacePool.max_le (retain_resident_le N count path.1)
    ((NativeFactorScan.Scope.code_resident_le source (visitInputs N count)
      (resultRef N count) path.2).trans (post_resident_capacity N count))

/-- The actual complete Shor code counts all quantum and classical resident capacity. -/
theorem code_resident_le {N : Nat} (source : Input N) (count : Nat)
    (path : (code source count).Path) :
    (code source count).peakResidentSpace path ≤ spaceBudget N count := by
  refine (Circuit.peakResidentSpace_seq (NativePreparedBatch.code pre pre_quantumWires N count)
    (recoveryStage source count) path).le.trans ?_
  exact SpacePool.max_le (sampling_resident_le N count path.1)
    (recovery_resident_le source count path.2)

private theorem pre_auxiliary : pre.auxiliarySpace = 0 := by
  apply SpacePool.ext
  intro axis
  cases axis <;> rfl

private theorem bank_auxiliary (N : Nat) :
    (NativeBank.context pre pre_quantumWires N).auxiliarySpace = bankSpace N := by
  rw [NativeBank.auxiliary, pre_auxiliary, add_zero]
  apply SpacePool.ext
  intro axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension => exact NativeQuantum.runtimeLayout_dimensionCount N dimension

private theorem sampled_auxiliary (N count : Nat) :
    (sampledContext N count).auxiliarySpace =
      bankSpace N + SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1))) := by
  change (NativePreparedBatch.context pre pre_quantumWires N count).auxiliarySpace = _
  rw [NativePreparedBatch.context_auxiliary, bank_auxiliary]

private theorem sampled_auxiliary_capacity (N count : Nat) :
    (sampledContext N count).auxiliarySpace ≤ spaceBudget N count := by
  rw [sampled_auxiliary]
  intro axis
  cases axis <;> simp [bankSpace, SpacePool.ofShape, spaceBudget]
  omega

private theorem post_auxiliary (N count : Nat) :
    (post N count).auxiliarySpace = SpacePool.ofShape (outputShape N) +
      (bankSpace N + SpacePool.ofShape (.bits (count * (22 * modulusBits N + 1)))) := by
  rw [post, RuntimeCtx.auxiliarySpace_addRetained, sampled_auxiliary]

private theorem post_auxiliary_capacity (N count : Nat) :
    (post N count).auxiliarySpace + NativeFactorScan.Scope.spaceBound .quantum N ≤
      spaceBudget N count := by
  rw [post_auxiliary, NativeFactorScan.Scope.spaceBound_eq]
  intro axis
  cases axis <;> simp [outputShape, bankSpace, SpacePool.ofShape, spaceBudget]
  omega

private theorem sampling_auxiliary_le (N count : Nat)
    (path : (NativePreparedBatch.code pre pre_quantumWires N count).Path) :
    (NativePreparedBatch.code pre pre_quantumWires N count).peakAuxiliarySpace path ≤
      spaceBudget N count := by
  have actual := NativePreparedBatch.auxiliary_le pre pre_quantumWires N count path
  rw [bank_auxiliary] at actual
  refine actual.trans ?_
  intro axis
  cases axis with
  | classicalBits => exact (Nat.zero_add _).le.trans (batch_allowance N count)
  | quantumSystems dimension => exact le_rfl

private theorem retain_auxiliary_le (N count : Nat)
    (path : (Circuit.retain (sampledContext N count) (resultKey N count)
      (outputShape N) (resultFresh N count)).Path) :
    (Circuit.retain (sampledContext N count) (resultKey N count)
      (outputShape N) (resultFresh N count)).peakAuxiliarySpace path ≤ spaceBudget N count := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  have location : visited = sampledContext N count ∨ visited = post N count := by
    change visited ∈ [sampledContext N count, post N count] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using present
  rcases location with old | retained
  · subst visited
    exact sampled_auxiliary_capacity N count
  · subst visited
    exact (show (post N count).auxiliarySpace ≤
      (post N count).auxiliarySpace + NativeFactorScan.Scope.spaceBound .quantum N from
        fun _ => Nat.le_add_right _ _).trans (post_auxiliary_capacity N count)

private theorem recovery_auxiliary_le {N : Nat} (source : Input N) (count : Nat)
    (path : (recoveryStage source count).Path) :
    (recoveryStage source count).peakAuxiliarySpace path ≤ spaceBudget N count := by
  refine (Circuit.peakAuxiliarySpace_seq
    (.retain (sampledContext N count) (resultKey N count) (outputShape N) (resultFresh N count))
    (recoveryCode source count) path).le.trans ?_
  exact SpacePool.max_le (retain_auxiliary_le N count path.1)
    ((NativeFactorScan.Scope.code_auxiliary_le source (visitInputs N count)
      (resultRef N count) path.2).trans (post_auxiliary_capacity N count))

/-- The actual complete Shor code counts all quantum and classical auxiliary capacity. -/
theorem code_auxiliary_le {N : Nat} (source : Input N) (count : Nat)
    (path : (code source count).Path) :
    (code source count).peakAuxiliarySpace path ≤ spaceBudget N count := by
  refine (Circuit.peakAuxiliarySpace_seq (NativePreparedBatch.code pre pre_quantumWires N count)
    (recoveryStage source count) path).le.trans ?_
  exact SpacePool.max_le (sampling_auxiliary_le N count path.1)
    (recovery_auxiliary_le source count path.2)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
