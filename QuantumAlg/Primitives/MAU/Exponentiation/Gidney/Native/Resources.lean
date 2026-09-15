/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Program
import all QuantumAlg.Core.Execution.Trace

/-!
# Independent native preparation and oracle resource contract

The preparation coordinate belongs to the declared two-word basis operation.
The remaining pool is the independent compute-copy-uncompute budget. The
resident and owned auxiliary peaks count the same exponent and three data
words, all retained at the output. Initialization is an actual charged step.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.OwnedQubits

/-- Independent preparation coordinate plus the separate oracle event budget. -/
def preparedNativeBudget (exponentWidth width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) : ResourcePool .quantum :=
  ResourcePool.singleton (workPreparation exponentWidth width modulus positive).event +
    oracleNativeBudget exponentWidth width

private theorem work_space (exponentWidth width : Nat) :
    SpacePool.ofQuantumLayout (workLayout exponentWidth width) = space (width + width) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (workQubitLayout exponentWidth width).toQuantumLayout_dimensionCount dimension

private theorem complete_space (exponentWidth width : Nat) :
    space (width + width) + space (exponentWidth + width) =
      space (exponentWidth + 3 * width) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then width + width else 0) +
        (if (2 : ℕ+) = dimension then exponentWidth + width else 0) =
          if (2 : ℕ+) = dimension then exponentWidth + 3 * width else 0
      split_ifs <;> omega

private theorem input_space_le (exponentWidth width : Nat) :
    space (exponentWidth + width) ≤ space (exponentWidth + 3 * width) := by
  intro axis
  cases axis with
  | classicalBits => exact Nat.le_refl 0
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then exponentWidth + width else 0) ≤
        if (2 : ℕ+) = dimension then exponentWidth + 3 * width else 0
      split_ifs <;> omega

theorem gidneyExponentPreparedContext_resident (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).residentSpace = space (exponentWidth + 3 * width) := by
  rw [preparedContext, RuntimeCtx.residentSpace_addOwnedLayout, work_space,
    ownedQubits_resident, complete_space]

theorem gidneyExponentPreparedContext_auxiliary (exponentWidth width : Nat) :
    (preparedContext exponentWidth width).auxiliarySpace = space (exponentWidth + 3 * width) := by
  rw [preparedContext, RuntimeCtx.auxiliarySpace_addOwnedLayout, work_space,
    ownedQubits_auxiliary, complete_space]

/-- The actual preparation and oracle trace satisfy every independent native coordinate bound. -/
theorem gidneyExponentNativeCode_native_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ)
    (path : (nativeCode exponentWidth width modulus positive base).Path) :
    (nativeCode exponentWidth width modulus positive base).resourcePool path ≤
      preparedNativeBudget exponentWidth width modulus positive := by
  change ResourcePool.ofList
    ([(workPreparation exponentWidth width modulus positive).event] ++
      (nativeUnitary exponentWidth width modulus base).eventTrace) ≤ _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    gidneyExponentNativeUnitary_eventCost]
  exact add_le_add
    (le_refl (ResourcePool.singleton (workPreparation exponentWidth width modulus positive).event))
    (gidneyExponentOracle_native_bound exponentWidth width modulus base)

theorem gidneyExponentNativeCode_resident_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ)
    (path : (nativeCode exponentWidth width modulus positive base).Path) :
    (nativeCode exponentWidth width modulus positive base).peakResidentSpace path ≤
      space (exponentWidth + 3 * width) := by
  intro axis
  change Nat.max ((context (exponentWidth + width)).residentSpace axis)
    (Nat.max ((preparedContext exponentWidth width).residentSpace axis)
      (Nat.max ((preparedContext exponentWidth width).residentSpace axis) 0)) ≤ _
  rw [ownedQubits_resident, gidneyExponentPreparedContext_resident]
  exact Nat.max_le.mpr ⟨input_space_le exponentWidth width axis,
    Nat.max_le.mpr ⟨le_rfl, Nat.max_le.mpr ⟨le_rfl, Nat.zero_le _⟩⟩⟩

theorem gidneyExponentNativeCode_auxiliary_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ)
    (path : (nativeCode exponentWidth width modulus positive base).Path) :
    (nativeCode exponentWidth width modulus positive base).peakAuxiliarySpace path ≤
      space (exponentWidth + 3 * width) := by
  intro axis
  change Nat.max ((context (exponentWidth + width)).auxiliarySpace axis)
    (Nat.max ((preparedContext exponentWidth width).auxiliarySpace axis)
      (Nat.max ((preparedContext exponentWidth width).auxiliarySpace axis) 0)) ≤ _
  rw [ownedQubits_auxiliary, gidneyExponentPreparedContext_auxiliary]
  exact Nat.max_le.mpr ⟨input_space_le exponentWidth width axis,
    Nat.max_le.mpr ⟨le_rfl, Nat.max_le.mpr ⟨le_rfl, Nat.zero_le _⟩⟩⟩

/-- Unit-duration depth includes the actual preparation, including empty work layouts. -/
theorem gidneyExponentNativeCode_depth_bound (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ)
    (path : (nativeCode exponentWidth width modulus positive base).Path) :
    (nativeCode exponentWidth width modulus positive base).depth (fun _ => 1) path ≤
      1 + oracleEventBound exponentWidth width := by
  change 1 + (nativeUnitary exponentWidth width modulus base).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [gidneyExponentNativeUnitary_depth]
  exact Nat.add_le_add_left (gidneyExponentOracle_depth_bound exponentWidth width modulus base) 1

end

end QuantumAlg.MAU.Exponentiation.Gidney
