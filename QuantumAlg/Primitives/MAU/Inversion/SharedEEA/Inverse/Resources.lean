/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Budget
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual prepared standalone inverse resources

The standalone XOR interface allocates the original shared-frame complement
beside its two supplied words, then executes the complete compute, copy, and
inverse program [LYL+26, sec_EEA/sub_4phase.tex:104-128]. Its fixed preparation
and every native gate occurrence are charged. The independent six-coordinate
envelope includes every corrected phase, terminal clock operation, decoder,
and inverse cleanup. The project extends the source prime domain to positive
moduli; modulus one retains the actual preparation and every live auxiliary
while its subsequent identity has no native events. The budget does not reuse
the paper's unverified leading constant.

For n = size(N), the complete live space is 3*n + 4*size(n) + 11 qubits and
zero classical bits. Every prepared system remains in the complete Output.
This standalone target word is not part of the smaller in-place forward
interface used for measured division [LYL+26, sec_point_add/sec_point_add.tex:51-79].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseResources

noncomputable section

open Execution InversePreparation

/-- The full standalone live register includes the input, XOR target, and original auxiliaries. -/
def width (inputWidth : Nat) : Nat := 3 * inputWidth + 4 * inputWidth.size + 11

/-- Native dimensions are counted directly; there is no classical storage or hidden reference. -/
def space (inputWidth : Nat) : SpacePool .quantum := OwnedQubits.space (width inputWidth)

/-- One fixed preparation coordinate and the independent complete native inverse envelope. -/
def events (modulus : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (InputPreparation.preparation modulus).event +
    NativeBudget.xor modulus.size

/-- The same sequential preparation and inverse meet this independent unit-duration bound. -/
def depthBound (inputWidth : Nat) : Nat := 1 + ForwardResources.xorBound inputWidth

private theorem auxiliary_space (inputWidth : Nat) :
    SpacePool.ofQuantumLayout (InputPreparation.auxiliaryLayout inputWidth) =
      OwnedQubits.space (InputPreparation.auxiliaryWidth inputWidth) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (InputPreparation.auxiliaryQubitLayout inputWidth).toQuantumLayout_dimensionCount
        dimension

/-- The input context contains exactly the two supplied words at their actual native dimension. -/
theorem before_resident (inputWidth : Nat) :
    (before inputWidth).residentSpace = OwnedQubits.space (inputWidth + inputWidth) := by
  simp only [before, RuntimeCtx.residentSpace_addOwnedLayout, RuntimeCtx.residentSpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (inputQubitLayout inputWidth).toQuantumLayout_dimensionCount dimension

/-- The supplied words have the owned role and are counted in the same auxiliary pool. -/
theorem before_auxiliary (inputWidth : Nat) :
    (before inputWidth).auxiliarySpace = OwnedQubits.space (inputWidth + inputWidth) := by
  simp only [before, RuntimeCtx.auxiliarySpace_addOwnedLayout, RuntimeCtx.auxiliarySpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (inputQubitLayout inputWidth).toQuantumLayout_dimensionCount dimension

private theorem combined_space (inputWidth : Nat) :
    OwnedQubits.space (InputPreparation.auxiliaryWidth inputWidth) +
      OwnedQubits.space (inputWidth + inputWidth) = space inputWidth := by
  have count : InputPreparation.auxiliaryWidth inputWidth + (inputWidth + inputWidth) =
      width inputWidth := by
    unfold InputPreparation.auxiliaryWidth InputPreparation.prefixWidth
      InputPreparation.suffixWidth width
    omega
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then _ else 0) +
        (if (2 : ℕ+) = dimension then _ else 0) =
          if (2 : ℕ+) = dimension then _ else 0
      split_ifs
      · exact count
      · rfl

/-- The complete post-context retains every actual allocated system. -/
theorem after_resident (inputWidth : Nat) :
    (after inputWidth).residentSpace = space inputWidth := by
  rw [after, RuntimeCtx.residentSpace_addOwnedLayout, auxiliary_space, before_resident]
  exact combined_space inputWidth

/-- Owned auxiliary accounting includes exactly those same live systems, with no extra bank. -/
theorem after_auxiliary (inputWidth : Nat) :
    (after inputWidth).auxiliarySpace = space inputWidth := by
  rw [after, RuntimeCtx.auxiliarySpace_addOwnedLayout, auxiliary_space, before_auxiliary]
  exact combined_space inputWidth

private theorem input_le (inputWidth : Nat) :
    OwnedQubits.space (inputWidth + inputWidth) ≤ space inputWidth := by
  have count : inputWidth + inputWidth ≤ width inputWidth := by
    unfold width
    omega
  intro axis
  cases axis with
  | classicalBits => exact le_rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then _ else 0) ≤
        if (2 : ℕ+) = dimension then width inputWidth else 0
      split_ifs
      · exact count
      · exact le_rfl

/-- The actual path visits preparation's two contexts and the complete native unitary context. -/
theorem visitedContexts (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).visitedContexts path =
      [before modulus.size, after modulus.size, after modulus.size] := by
  rfl

private theorem prepend_pool (event : Resource.Event .quantum)
    (trace : List (Resource.Event .quantum)) (bound : ResourcePool .quantum)
    (bounded : ResourcePool.ofList trace ≤ bound) :
    ResourcePool.ofList (event :: trace) ≤ ResourcePool.singleton event + bound := by
  rw [ResourcePool.ofList_cons]
  simpa only [add_comm] using add_le_add_left bounded (ResourcePool.singleton event)

private theorem native_pool (modulus : Nat) :
    (InverseRuntime.nativeProgram modulus).eventCost ≤ NativeBudget.xor modulus.size := by
  by_cases nontrivial : 1 < modulus
  · simpa only [InverseRuntime.nativeProgram, dif_pos nontrivial] using
      NativeBudget.xor_bound modulus nontrivial
  · simp only [InverseRuntime.nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost]
    exact zero_le

/-- Every actual event multiplicity is bounded at its native preparation or gate coordinate. -/
theorem resourcePool (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).resourcePool path ≤ events modulus := by
  have native : ResourcePool.ofList (InverseRuntime.nativeProgram modulus).eventTrace ≤
      NativeBudget.xor modulus.size :=
    (UnitaryCircuit.ofList_eventTrace_eq_eventCost (InverseRuntime.nativeProgram modulus)).le.trans
      (native_pool modulus)
  have bounded := prepend_pool (InputPreparation.preparation modulus).event
    (InverseRuntime.nativeProgram modulus).eventTrace (NativeBudget.xor modulus.size) native
  exact (congrArg ResourcePool.ofList
    (InverseRuntime.code_eventTrace modulus path)).le.trans bounded

/-- Resident capacity is obtained from the same actual visited contexts. -/
theorem resident (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).peakResidentSpace path ≤ space modulus.size := by
  unfold Circuit.peakResidentSpace
  rw [visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, after_resident,
    SpacePool.max_zero, SpacePool.max_self, before_resident]
  exact SpacePool.max_le (input_le modulus.size) le_rfl

/-- Owned auxiliary capacity is obtained from those same actual visited contexts. -/
theorem auxiliary (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).peakAuxiliarySpace path ≤ space modulus.size := by
  unfold Circuit.peakAuxiliarySpace
  rw [visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, after_auxiliary,
    SpacePool.max_zero, SpacePool.max_self, before_auxiliary]
  exact SpacePool.max_le (input_le modulus.size) le_rfl

private theorem prepared_depth {ctx : RuntimeCtx .quantum} {count : Nat}
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout)
    (unitary : UnitaryCircuit (ctx.addOwnedLayout key layout fresh disjoint).register)
    (placement : unitary.physical_idx =
      (ctx.addOwnedLayout key layout fresh disjoint).physicalIdx)
    (bound : Nat) (bounded : unitary.eventCost.card ≤ bound)
    (path : ((Circuit.prepare ctx key layout fresh disjoint preparation).seq
      (Circuit.unitary unitary placement)).Path) :
    ((Circuit.prepare ctx key layout fresh disjoint preparation).seq
      (Circuit.unitary unitary placement)).depth (fun _ => 1) path ≤ 1 + bound := by
  change 1 + unitary.evaluatedEventDepth (fun _ => 1) ≤ 1 + bound
  exact Nat.add_le_add_left ((ShiftResources.unitDepth_le_count unitary).trans bounded) 1

private theorem native_count (modulus : Nat) :
    (InverseRuntime.nativeProgram modulus).eventCost.card ≤
      ForwardResources.xorBound modulus.size := by
  by_cases nontrivial : 1 < modulus
  · simpa only [InverseRuntime.nativeProgram, dif_pos nontrivial] using
      ForwardResources.xor_count modulus nontrivial
  · simp only [InverseRuntime.nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost, Multiset.card_zero]
    exact Nat.zero_le _

/-- Preparation precedes the actual unitary; modulus one still pays its preparation event. -/
theorem depth (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).depth (fun _ => 1) path ≤ depthBound modulus.size := by
  have ledger : (InverseRuntime.program modulus).eventCost =
      (InverseRuntime.nativeProgram modulus).eventCost :=
    InverseRuntimeFrame.program_eventCost modulus.size (InverseRuntime.nativeProgram modulus)
  have bounded := (congrArg Multiset.card ledger).le.trans (native_count modulus)
  exact prepared_depth auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
    (InputPreparation.preparation modulus) (InverseRuntime.program modulus)
    (InverseRuntime.program_physical modulus) (ForwardResources.xorBound modulus.size)
    bounded path

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseResources
