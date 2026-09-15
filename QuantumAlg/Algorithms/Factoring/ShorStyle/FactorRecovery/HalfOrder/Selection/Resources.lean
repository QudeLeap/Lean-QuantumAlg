/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Resources
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange.Resources

/-!
# Independent native budgets of the actual left-priority factor selector

The left GCD and its range check precede a real stored-bit branch. Only left
rejection executes the right GCD and its range check. Either arm then executes
one real resize and one nominal option pack. The independent budget admits
both GCDs and checks while counting that packaging only once.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The two actual representation operations performed by either selected final arm. -/
def packBudget (kind : ProblemKind) (N : Nat) : ResourcePool kind :=
  ResourcePool.ofList
    [.classicalOperation (.wordResize (modulusBits N + 1) (modulusBits N)),
      .classicalOperation (.nominalEncoding (.packOption (modulusBits N)))]

/-- The real right-rejection continuation includes its own GCD, range check and final pack. -/
def rightEnvelope (kind : ProblemKind) (N : Nat) : ResourcePool kind :=
  NativeHalfGCD.eventEnvelope kind true N +
    (FactorRange.eventBudget kind (modulusBits N + 1) + packBudget kind N)

/-- Independent actual-operation coordinates for both possible source GCD candidates. -/
def eventEnvelope (kind : ProblemKind) (N : Nat) : ResourcePool kind :=
  NativeHalfGCD.eventEnvelope kind false N +
    (FactorRange.eventBudget kind (modulusBits N + 1) + rightEnvelope kind N)

/-- All serial native dependencies of both GCDs, both checks and the sole final packaging. -/
def depthBound (N : Nat) : Nat :=
  NativeHalfGCD.depthBound false N + 3 + (NativeHalfGCD.depthBound true N + 5)

private theorem pack_pool (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (pack cells output).Path) :
    (pack cells output).resourcePool path = packBudget kind N :=
  congrArg ResourcePool.ofList (pack_eventTrace cells output path)

private theorem pack_budget_le : packBudget kind N ≤ rightEnvelope kind N :=
  (le_add_of_nonneg_left
    (zero_le : (0 : ResourcePool kind) ≤ FactorRange.eventBudget kind (modulusBits N + 1))).trans
      (le_add_of_nonneg_left
        (zero_le : (0 : ResourcePool kind) ≤ NativeHalfGCD.eventEnvelope kind true N))

private theorem right_pool_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (right halfPower cells output).Path) :
    (right halfPower cells output).resourcePool path ≤ rightEnvelope kind N := by
  change ResourcePool.ofList
    ((NativeHalfGCD.code (N := N) true halfPower cells.candidate).eventTrace path.1 ++
      ((FactorRange.code (checkRefs cells)).eventTrace path.2.1 ++
        (pack cells output).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (NativeHalfGCD.code_pool_le true halfPower cells.candidate path.1)
    (add_le_add (FactorRange.code_pool (checkRefs cells) path.2.1).le
      (pack_pool cells output path.2.2).le)

private theorem choose_pool_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (choose halfPower cells output).Path) :
    (choose halfPower cells output).resourcePool path ≤ rightEnvelope kind N := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact right_pool_le halfPower cells output path
      · exact (pack_pool cells output path).le.trans pack_budget_le

/-- The selected actual factor-recovery path fits the independent native coordinate ledger. -/
theorem code_pool_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower cells output).Path) :
    (code halfPower cells output).resourcePool path ≤ eventEnvelope kind N := by
  change ResourcePool.ofList
    ((NativeHalfGCD.code (N := N) false halfPower cells.candidate).eventTrace path.1 ++
      ((FactorRange.code (checkRefs cells)).eventTrace path.2.1 ++
        (choose halfPower cells output).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (NativeHalfGCD.code_pool_le false halfPower cells.candidate path.1)
    (add_le_add (FactorRange.code_pool (checkRefs cells) path.2.1).le
      (choose_pool_le halfPower cells output path.2.2))

private theorem right_unitDepth_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (right halfPower cells output).Path) :
    (right halfPower cells output).depth (fun _ => 1) path ≤
      NativeHalfGCD.depthBound true N + 5 := by
  have gcd := NativeHalfGCD.code_unitDepth_le true halfPower cells.candidate path.1
  have check := FactorRange.code_unitDepth (checkRefs cells) path.2.1
  change (NativeHalfGCD.code (N := N) true halfPower cells.candidate).depth
    (fun _ => 1) path.1 + ((FactorRange.code (checkRefs cells)).depth
      (fun _ => 1) path.2.1 + 2) ≤ _
  omega

private theorem choose_unitDepth_le
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (choose halfPower cells output).Path) :
    (choose halfPower cells output).depth (fun _ => 1) path ≤
      NativeHalfGCD.depthBound true N + 5 := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact right_unitDepth_le halfPower cells output path
      · change 2 ≤ NativeHalfGCD.depthBound true N + 5
        omega

/-- The depth bound includes every selected serial arithmetic and packaging dependency. -/
theorem code_unitDepth_le (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (code halfPower cells output).Path) :
    (code halfPower cells output).depth (fun _ => 1) path ≤ depthBound N := by
  have gcd := NativeHalfGCD.code_unitDepth_le false halfPower cells.candidate path.1
  have check := FactorRange.code_unitDepth (checkRefs cells) path.2.1
  have selected := choose_unitDepth_le halfPower cells output path.2.2
  change (NativeHalfGCD.code (N := N) false halfPower cells.candidate).depth
    (fun _ => 1) path.1 + ((FactorRange.code (checkRefs cells)).depth
      (fun _ => 1) path.2.1 + (choose halfPower cells output).depth
        (fun _ => 1) path.2.2) ≤ _
  unfold depthBound
  omega

/-- The independent depth formula is linear in the actual widened GCD width. -/
theorem depthBound_eq (N : Nat) : depthBound N = 24 * (modulusBits N + 1) + 35 := by
  unfold depthBound NativeHalfGCD.depthBound
  simp only [Bool.false_eq_true, if_false, if_true]
  omega

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
