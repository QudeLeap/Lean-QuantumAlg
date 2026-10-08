/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Program
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Native resources of internally prepared unit multiplication

The independent pool permits one zero-word preparation followed by the
already specified unit-multiplier pool. The source and newly allocated word
give a resident peak of `2 * width` actual qubits. Both are owned, so the
owned auxiliary coordinate describes those same systems. Unit-duration
depth includes the preparation before the serial native gate sequence.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Execution.OwnedQubits

/-- Independent native event pool: the declared zero preparation plus the multiplier budget. -/
def preparedNativeBudget (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ZeroPreparation.eventCost AlgorithmGate.model .empty (auxiliaryLayout width) +
    nativeBudget width

private theorem auxiliary_space (width : Nat) :
    SpacePool.ofQuantumLayout (auxiliaryLayout width) = space width := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (auxiliaryQubitLayout width).toQuantumLayout_dimensionCount dimension

private theorem two_word_space (width : Nat) : space width + space width = space (2 * width) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then width else 0) +
        (if (2 : ℕ+) = dimension then width else 0) =
          if (2 : ℕ+) = dimension then 2 * width else 0
      split_ifs <;> omega

private theorem input_space_le (width : Nat) : space width ≤ space (2 * width) := by
  intro axis
  cases axis with
  | classicalBits => exact Nat.le_refl 0
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then width else 0) ≤
        if (2 : ℕ+) = dimension then 2 * width else 0
      split_ifs <;> omega

theorem gidneyPreparedContext_resident (width : Nat) :
    (preparedContext width).residentSpace = space (2 * width) := by
  rw [preparedContext, RuntimeCtx.residentSpace_addOwnedLayout, auxiliary_space,
    ownedQubits_resident, two_word_space]

theorem gidneyPreparedContext_auxiliary (width : Nat) :
    (preparedContext width).auxiliarySpace = space (2 * width) := by
  rw [preparedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout, auxiliary_space,
    ownedQubits_auxiliary, two_word_space]

/-- The actual preparation and gate trace satisfy the independent coordinatewise pool. -/
theorem gidneyPreparedCode_native_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (path : (preparedCode width modulus coefficient).Path) :
    (preparedCode width modulus coefficient).resourcePool path ≤ preparedNativeBudget width := by
  change ResourcePool.ofList
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty (auxiliaryLayout width) ++
      (preparedUnitary width modulus coefficient).eventTrace) ≤ _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    gidneyPreparedUnitary_eventCost]
  exact add_le_add
    (le_refl (ZeroPreparation.eventCost AlgorithmGate.model .empty (auxiliaryLayout width)))
    (gidneyUnitMultiplication_native_bound width modulus coefficient)

theorem gidneyPreparedCode_resident_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (path : (preparedCode width modulus coefficient).Path) :
    (preparedCode width modulus coefficient).peakResidentSpace path ≤ space (2 * width) := by
  intro axis
  change Nat.max ((context width).residentSpace axis)
    (Nat.max ((preparedContext width).residentSpace axis)
      (Nat.max ((preparedContext width).residentSpace axis) 0)) ≤ space (2 * width) axis
  rw [ownedQubits_resident, gidneyPreparedContext_resident]
  exact Nat.max_le.mpr ⟨input_space_le width axis,
    Nat.max_le.mpr ⟨le_rfl, Nat.max_le.mpr ⟨le_rfl, Nat.zero_le _⟩⟩⟩

theorem gidneyPreparedCode_auxiliary_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (path : (preparedCode width modulus coefficient).Path) :
    (preparedCode width modulus coefficient).peakAuxiliarySpace path ≤ space (2 * width) := by
  intro axis
  change Nat.max ((context width).auxiliarySpace axis)
    (Nat.max ((preparedContext width).auxiliarySpace axis)
      (Nat.max ((preparedContext width).auxiliarySpace axis) 0)) ≤ space (2 * width) axis
  rw [ownedQubits_auxiliary, gidneyPreparedContext_auxiliary]
  exact Nat.max_le.mpr ⟨input_space_le width axis,
    Nat.max_le.mpr ⟨le_rfl, Nat.max_le.mpr ⟨le_rfl, Nat.zero_le _⟩⟩⟩

/-- The actual serial depth includes one preparation layer when the word is nonempty. -/
theorem gidneyPreparedCode_depth_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (path : (preparedCode width modulus coefficient).Path) :
    (preparedCode width modulus coefficient).depth (fun _ => 1) path ≤ 1 + eventBound width := by
  change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model .empty (auxiliaryLayout width)) +
    (preparedUnitary width modulus coefficient).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [ZeroPreparation.zeroPreparation_uniform_unit_depth AlgorithmGate.model .empty
      (auxiliaryLayout width) 2 (fun _ => rfl), gidneyPreparedUnitary_depth]
  have actual := gidneyUnitMultiplication_depth_bound width modulus coefficient
  split_ifs <;> omega

end

end QuantumAlg.MAU.Multiplication.Gidney
