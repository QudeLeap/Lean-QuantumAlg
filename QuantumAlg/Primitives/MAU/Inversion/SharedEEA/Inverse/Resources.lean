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
import all QuantumAlg.Core.Execution.Preparation.Resources

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

/-- Independently count the set bits in the fixed mathematical seed. -/
def seedEvents (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  EncodedBit.Word.BasisLoad.xCount (InputPreparation.loadConstant modulus) •
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit)

/-- Every allocated zero wire, fixed-seed X and complete native inverse is charged. -/
def events (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
    seedEvents modulus + NativeBudget.xor modulus.size

/-- Independent sequential duration allowance for zero allocation, X loading and inversion. -/
def depthBound (inputWidth : Nat) : Nat :=
  1 + InputPreparation.auxiliaryWidth inputWidth + ForwardResources.xorBound inputWidth

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

/-- The actual path visits the supplied words, zero allocation, seed loading and inverse. -/
theorem visitedContexts (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).visitedContexts path =
      [before modulus.size, after modulus.size, after modulus.size,
        after modulus.size] := by
  rfl

private theorem native_pool (modulus : Nat) :
    (InverseRuntime.nativeProgram modulus).eventCost ≤ NativeBudget.xor modulus.size := by
  by_cases nontrivial : 1 < modulus
  · simpa only [InverseRuntime.nativeProgram, dif_pos nontrivial,
      NativeInverse.nativeInverse_nativeProgram_eventCost] using
      NativeBudget.xor_bound modulus nontrivial
  · simp only [InverseRuntime.nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost]
    exact zero_le

private theorem load_pool (modulus : Nat) :
    (InversePreparation.loadProgram modulus).eventCost = seedEvents modulus := by
  have placed := Execution.PreparationLoaded.program_eventCost (before modulus.size)
    auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
    (EncodedBit.Word.BasisLoad.program (InputPreparation.auxiliaryQubitLayout modulus.size)
      .empty (InputPreparation.loadConstant modulus))
  exact placed.trans (EncodedBit.Word.BasisLoad.basisLoad_eventCost
    (InputPreparation.auxiliaryQubitLayout modulus.size) .empty
    (InputPreparation.loadConstant modulus))

private theorem add_bound {left right : ResourcePool (.quantum AlgorithmGate.model .empty)}
    (head : ResourcePool (.quantum AlgorithmGate.model .empty))
    (bounded : left ≤ right) : head + left ≤ head + right :=
  add_le_add_right bounded head

/-- Every actual preparation, fixed X and native event is bounded independently. -/
theorem resourcePool (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).resourcePool path ≤ events modulus := by
  change ResourcePool.ofList ((InverseRuntime.code modulus).eventTrace path) ≤ _
  rw [InverseRuntime.code_eventTrace, ResourcePool.ofList_append,
    ResourcePool.ofList_append]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
    ResourcePool.ofList (InversePreparation.loadProgram modulus).eventTrace +
    ResourcePool.ofList (InverseRuntime.nativeProgram modulus).eventTrace ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, load_pool,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) + seedEvents modulus +
        (InverseRuntime.nativeProgram modulus).eventCost ≤
    ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) + seedEvents modulus +
        NativeBudget.xor modulus.size
  exact add_bound
    (ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) + seedEvents modulus)
    (native_pool modulus)

/-- Resident capacity is obtained from all actual visited contexts. -/
theorem resident (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).peakResidentSpace path ≤ space modulus.size := by
  unfold Circuit.peakResidentSpace
  rw [visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, after_resident,
    SpacePool.max_zero, SpacePool.max_self, before_resident]
  exact SpacePool.max_le (input_le modulus.size) le_rfl

/-- Owned auxiliary capacity is obtained from those same actual contexts. -/
theorem auxiliary (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).peakAuxiliarySpace path ≤ space modulus.size := by
  unfold Circuit.peakAuxiliarySpace
  rw [visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil, after_auxiliary,
    SpacePool.max_zero, SpacePool.max_self, before_auxiliary]
  exact SpacePool.max_le (input_le modulus.size) le_rfl

private theorem native_count (modulus : Nat) :
    (InverseRuntime.nativeProgram modulus).eventCost.card ≤
      ForwardResources.xorBound modulus.size := by
  by_cases nontrivial : 1 < modulus
  · simpa only [InverseRuntime.nativeProgram, dif_pos nontrivial,
      NativeInverse.nativeInverse_nativeProgram_eventCost] using
      ForwardResources.xor_count modulus nontrivial
  · simp only [InverseRuntime.nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost, Multiset.card_zero]
    exact Nat.zero_le _

/-- Zero allocation, literal seed loading and native arithmetic obey the same bound. -/
theorem depth (modulus : Nat)
    (path : (InverseRuntime.code modulus).Path) :
    (InverseRuntime.code modulus).depth (fun _ => 1) path ≤
      depthBound modulus.size := by
  have zeroBound :
      (if InputPreparation.auxiliaryWidth modulus.size = 0 then 0 else 1) ≤ 1 := by
    split_ifs <;> omega
  have loadBound := (InversePreparation.loadProgram_resources modulus).2
  have nativeBound :
      (InverseRuntime.program modulus).evaluatedEventDepth (fun _ => 1) ≤
        ForwardResources.xorBound modulus.size := by
    exact (ShiftResources.unitDepth_le_count (InverseRuntime.program modulus)).trans
      ((congrArg Multiset.card (InverseRuntime.program_eventCost modulus)).le.trans
        (native_count modulus))
  change
    DepthExpr.depthEval (fun _ => 1)
        (ZeroPreparation.eventDepth AlgorithmGate.model .empty
          (InputPreparation.auxiliaryLayout modulus.size)) +
      (InversePreparation.loadProgram modulus).evaluatedEventDepth (fun _ => 1) +
      (InverseRuntime.program modulus).evaluatedEventDepth (fun _ => 1) ≤
        depthBound modulus.size
  rw [ZeroPreparation.zeroPreparation_unit_depth]
  unfold depthBound
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseResources
