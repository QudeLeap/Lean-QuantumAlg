/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Native events and depth of the complete six-cell factor scope

The actual one and modulus words are loaded before the actual left-priority
GCD circuit. Both literal constant programs contribute their native shifts
and selected increments. Entering and releasing the six real cells adds no
hidden arithmetic events, while the serial bound includes every load step.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Independent native coordinates include both real constants and the full factor selector. -/
def eventEnvelope (kind : ProblemKind) (N : Nat) : ResourcePool kind :=
  ConstantWord.envelope kind (modulusBits N + 1) +
    (ConstantWord.envelope kind (modulusBits N + 1) + NativeHalfFactor.eventEnvelope kind N)

/-- Serial unit-depth allowance for both actual constant loads and the complete GCD selection. -/
def depthBound (N : Nat) : Nat := 28 * (modulusBits N + 1) + 35

/-- The complete actual scope path fits the independent native event ledger. -/
theorem code_pool_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower output).Path) :
    (code halfPower output).resourcePool path ≤ eventEnvelope kind N := by
  change ResourcePool.ofList
    ((ConstantWord.circuit (oneRef ctx N) 1).eventTrace path.1 ++
      ((ConstantWord.circuit (modulusRef ctx N) N).eventTrace path.2.1 ++
        (NativeHalfFactor.code (liftInput halfPower) (cells ctx N)
          (liftWrite output)).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (ConstantWord.constantWord_pool_le (oneRef ctx N) 1 path.1)
    (add_le_add (ConstantWord.constantWord_pool_le (modulusRef ctx N) N path.2.1)
      (NativeHalfFactor.code_pool_le (liftInput halfPower) (cells ctx N)
        (liftWrite output) path.2.2))

/-- The real serial path counts both loaded constants and every possible GCD dependency. -/
theorem code_unitDepth_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower output).Path) :
    (code halfPower output).depth (fun _ => 1) path ≤ depthBound N := by
  have one := ConstantWord.constantWord_depth_le (oneRef ctx N) 1 (fun _ => 1) path.1
  have modulus := ConstantWord.constantWord_depth_le (modulusRef ctx N) N (fun _ => 1) path.2.1
  have factors := NativeHalfFactor.code_unitDepth_le
    (liftInput halfPower) (cells ctx N) (liftWrite output) path.2.2
  rw [NativeHalfFactor.depthBound_eq] at factors
  change (ConstantWord.circuit (oneRef ctx N) 1).depth (fun _ => 1) path.1 ≤
    (modulusBits N + 1) * (1 + 1) at one
  change (ConstantWord.circuit (modulusRef ctx N) N).depth (fun _ => 1) path.2.1 ≤
    (modulusBits N + 1) * (1 + 1) at modulus
  change (ConstantWord.circuit (oneRef ctx N) 1).depth (fun _ => 1) path.1 +
    ((ConstantWord.circuit (modulusRef ctx N) N).depth (fun _ => 1) path.2.1 +
      (NativeHalfFactor.code (liftInput halfPower) (cells ctx N)
        (liftWrite output)).depth (fun _ => 1) path.2.2) ≤ _
  unfold depthBound
  omega

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
