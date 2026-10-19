/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Depth

/-!
# Native event and depth bounds of both actual half-power GCD calls

The independent ledger includes the chosen adjacent-value arithmetic, every
literal bit of the loaded modulus, the real result-clearing XOR and the
expanded Euclidean circuit. Both operand scopes are actual allocations and
add no arithmetic events. The following bounds hold for every actual path,
including inactive Euclidean iterations and either adjacent direction.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- Independent coordinates retain every initialization and actual Euclidean operation kind. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (successor : Bool) (N : Nat) :
  ResourcePool model :=
  NativeAdjacentWord.eventEnvelope model successor (modulusBits N) +
    (ConstantWord.envelope model (modulusBits N + 1) +
      (ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordBinary .bitXor (modulusBits N + 1)))) +
        NumberTheory.GCD.nativeEnvelope model (modulusBits N + 1)))

/-- Independent serial duration, including every constant-load bit and the real clearing XOR. -/
def depthBound (successor : Bool) (N : Nat) : Nat :=
  12 * (modulusBits N + 1) + 11 + if successor then 2 else 3

private lemma body_pool_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (body (model := model) successor halfPower output).Path) :
    (body (model := model) successor halfPower output).resourcePool path ≤ eventEnvelope model
      successor N := by
  change ResourcePool.ofList
    ((NativeAdjacentWord.code (model := model) successor (liftInput halfPower) (adjacentRef ctx
      N)).eventTrace
      path.1 ++ ((ConstantWord.circuit (model := model) (modulusRef ctx N) N).eventTrace path.2.1 ++
        (gcdTail (model := model) output).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, gcdTail_eventTrace]
  exact add_le_add
    (NativeAdjacentWord.code_pool_le successor (liftInput halfPower) (adjacentRef ctx N) path.1)
    (add_le_add (ConstantWord.constantWord_pool_le (modulusRef ctx N) N path.2.1)
      (add_le_add le_rfl
        (NumberTheory.GCD.gcdLexical_pool_le (operands ctx N) (liftWrite output) path.2.2.2)))

/-- Both real operand scopes preserve the complete independent native event bound. -/
lemma code_pool_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (code (model := model) successor halfPower output).Path) :
    (code (model := model) successor halfPower output).resourcePool path ≤ eventEnvelope model
      successor N :=
  body_pool_le successor halfPower output path

/-- Every native dependency is included in the actual adjacent, load, clear and GCD sequence. -/
lemma code_unitDepth_le (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (path : (code (model := model) successor halfPower output).Path) :
    (code (model := model) successor halfPower output).depth (fun _ => 1) path ≤ depthBound
      successor N := by
  have adjacent := NativeAdjacentWord.code_unitDepth_le (model := model) successor
    (liftInput halfPower) (adjacentRef ctx N) path.1
  have loaded := ConstantWord.constantWord_depth_le (model := model) (modulusRef ctx N) N
    (fun _ => 1) path.2.1
  have euclidean := NumberTheory.GCD.gcdLexical_depth_le (model := model) (operands ctx N)
    (liftWrite output) (fun _ => 1) path.2.2.2
  rw [NumberTheory.GCD.gcdNativeDepthLimit_unit] at euclidean
  change (NativeAdjacentWord.code (model := model) successor (liftInput halfPower) (adjacentRef
    ctx N)).depth
    (fun _ => 1) path.1 +
      ((ConstantWord.circuit (model := model) (modulusRef ctx N) N).depth (fun _ => 1) path.2.1 +
        (1 + (NumberTheory.GCD.lexicalBody (model := model) (operands ctx N) (liftWrite
          output)).depth
          (fun _ => 1) path.2.2.2)) ≤ _
  change (ConstantWord.circuit (model := model) (modulusRef ctx N) N).depth (fun _ => 1) path.2.1 ≤
    (modulusBits N + 1) * (1 + 1) at loaded
  unfold depthBound
  omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
