/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Core.Execution.Preparation.Loaded
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local

/-!
# Actual fixed auxiliary preparation beside the original quantum input

The original input occupies exactly the low n physical bits of Work2.
One actual preparation adds all remaining source wires: the n+6 positions
before that input and the four length fields and five controls after it
[LYL+26, sec_EEA/sub_regshare.tex:16-26; sec_EEA/sub_4phase.tex:104-117].
Its values depend only on the modulus: Work1 is `100,p`, its coefficient
length is one, and all remaining new bits are zero. The divisor length
will be computed by the actual native writer after the actual fold.

The preparation tensors these fixed finite values with the complete
unknown input-reference state [dW19, qcnotes.tex:5381,8071]. It does not
prepare from the input label or require any initial clean work from the
caller. Both coherent reference entries and the single actual preparation
event are retained. The later source-label and native-program connection
uses this same allocated frame.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputPreparation

noncomputable section

open Execution

/-- Work1 and the three zero padding positions preceding the original Work2 input. -/
def prefixWidth (width : Nat) : Nat := width + 6

/-- Exactly the actual four length fields and five controls following the input. -/
def suffixWidth (width : Nat) : Nat := 4 * width.size + 5

/-- Every new wire outside the supplied n-bit input, including the large source workspace. -/
def auxiliaryWidth (width : Nat) : Nat := prefixWidth width + suffixWidth width

/-- Keep each supplied input bit at its literal final source physical identity. -/
def inputQubitLayout (width : Nat) : QubitLayout width where
  physical_idx index := prefixWidth width + index.val
  physical_idx_injective := by
    intro left right same
    apply Fin.ext
    change prefixWidth width + left.val = prefixWidth width + right.val at same
    omega

/-- The supplied input consists of these actual dimension-two systems and no auxiliary wire. -/
def inputLayout (width : Nat) : QuantumLayout width :=
  (inputQubitLayout width).toQuantumLayout

/-- Enumerate the exact complement of the supplied contiguous input, in physical order. -/
def auxiliaryPhysicalIndex (width : Nat) (index : Fin (auxiliaryWidth width)) : Nat :=
  if index.val < prefixWidth width then index.val else width + index.val

private theorem auxiliaryPhysicalIndex_injective (width : Nat) :
    Function.Injective (auxiliaryPhysicalIndex width) := by
  intro left right same
  apply Fin.ext
  unfold auxiliaryPhysicalIndex at same
  split at same <;> split at same <;> omega

/-- The preparation uses only the existing source identities outside the original input. -/
def auxiliaryQubitLayout (width : Nat) : QubitLayout (auxiliaryWidth width) where
  physical_idx := auxiliaryPhysicalIndex width
  physical_idx_injective := auxiliaryPhysicalIndex_injective width

/-- Every added source system remains explicitly dimension two. -/
def auxiliaryLayout (width : Nat) : QuantumLayout (auxiliaryWidth width) :=
  (auxiliaryQubitLayout width).toQuantumLayout

/-- The algorithm starts with exactly one supplied owned input register. -/
def before (width : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (inputLayout width) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private theorem before_physical (width : Nat) :
    (before width).physicalIdx = (inputLayout width).identities := by
  change ((inputLayout width).wires ++ []).map QuantumWire.identity = _
  rw [List.append_nil, ← layout_identities_eq_map_wires]

private theorem input_wires (width : Nat) :
    (inputLayout width).wires = (before width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputLayout width).wires = (inputLayout width).wires ++ []
  exact (List.append_nil _).symm

/-- Binary labels identify exactly the originally supplied n physical bits. -/
def inputBasisEquiv (width : Nat) : (before width).register.Index ≃ (Qubits width).Index :=
  (basisOfEqualWires (inputLayout width) (before width).quantumLayout
    (input_wires width)).symm.trans (inputQubitLayout width).binaryIndexEquiv

private def auxiliaryKey : StorageKey := ⟨1⟩

private theorem auxiliary_fresh (width : Nat) : auxiliaryKey ∉ (before width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

private theorem auxiliary_disjoint (width : Nat) :
    List.Disjoint (auxiliaryLayout width).identities (before width).physicalIdx := by
  rw [before_physical]
  apply List.disjoint_left.mpr
  intro wire fresh old
  change wire ∈ List.ofFn (auxiliaryPhysicalIndex width) at fresh
  change wire ∈ List.ofFn (fun index : Fin width => prefixWidth width + index.val) at old
  obtain ⟨newIndex, newPosition⟩ := List.mem_ofFn.mp fresh
  obtain ⟨oldIndex, oldPosition⟩ := List.mem_ofFn.mp old
  have oldBound := oldIndex.isLt
  unfold auxiliaryPhysicalIndex at newPosition
  split at newPosition <;> omega

/-- Every original source wire is live after this fixed auxiliary preparation. -/
def after (width : Nat) : RuntimeCtx .quantum :=
  (before width).addOwnedLayout auxiliaryKey (auxiliaryLayout width)
    (auxiliary_fresh width) (auxiliary_disjoint width)

/-- Runtime order places fresh auxiliary systems before the unchanged original input. -/
theorem after_physical (width : Nat) :
    (after width).physicalIdx =
      (auxiliaryLayout width).identities ++ (inputLayout width).identities := by
  change ((auxiliaryLayout width).wires ++ (before width).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (auxiliaryLayout width).identities ++ (before width).physicalIdx = _
  rw [before_physical]

/-- The declared source encoding counts exactly the supplied input plus all newly prepared wires. -/
theorem complete_width (width : Nat) :
    width + auxiliaryWidth width = (encoding width).width := by
  rw [encoding_width]
  unfold auxiliaryWidth prefixWidth suffixWidth
  omega

/-- The actual live context contains every canonical native source address. -/
theorem range_contained (width : Nat) :
    List.range (encoding width).width ⊆ (after width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  have complete := complete_width width
  rw [after_physical]
  by_cases beforeInput : wire < prefixWidth width
  · apply List.mem_append.mpr
    left
    change wire ∈ List.ofFn (auxiliaryPhysicalIndex width)
    let index : Fin (auxiliaryWidth width) := ⟨wire, by
      unfold auxiliaryWidth
      omega⟩
    exact List.mem_ofFn.mpr ⟨index, by
      change (if wire < prefixWidth width then wire else width + wire) = wire
      rw [if_pos beforeInput]⟩
  · by_cases inInput : wire < prefixWidth width + width
    · apply List.mem_append.mpr
      right
      change wire ∈ List.ofFn (fun index : Fin width => prefixWidth width + index.val)
      let index : Fin width := ⟨wire - prefixWidth width, by omega⟩
      exact List.mem_ofFn.mpr ⟨index, by
        change prefixWidth width + (wire - prefixWidth width) = wire
        omega⟩
    · apply List.mem_append.mpr
      left
      change wire ∈ List.ofFn (auxiliaryPhysicalIndex width)
      let index : Fin (auxiliaryWidth width) := ⟨wire - width, by omega⟩
      exact List.mem_ofFn.mpr ⟨index, by
        change (if wire - width < prefixWidth width then wire - width
          else width + (wire - width)) = wire
        rw [if_neg (by omega)]
        omega⟩

/-- Fixed source initialization at a physical identity; no input value enters this function. -/
def fixedBit (modulus wire : Nat) : Bool :=
  if wire < modulus.size + 3 then
    (BitVec.ofNat (modulus.size + 3) (4 * 2 ^ modulus.size + modulus)).getMsbD wire
  else if 2 * (modulus.size + 3) ≤ wire ∧
      wire < 2 * (modulus.size + 3) + modulus.size.size then
    (BitVec.ofNat modulus.size.size 1).getMsbD (wire - 2 * (modulus.size + 3))
  else false

/-- Prepare the literal fixed auxiliary values on precisely their allocated physical systems. -/
def preparation (modulus : Nat) : BasisPreparation (auxiliaryLayout modulus.size) where
  value index := finTwoEquiv.symm (fixedBit modulus (auxiliaryPhysicalIndex modulus.size index))

/-- Encode the fixed source seed in the exact auxiliary wire order. -/
def loadConstant (modulus : Nat) : Fin (2 ^ auxiliaryWidth modulus.size) :=
  (auxiliaryQubitLayout modulus.size).binaryIndexEquiv (preparation modulus).value

/-- Literal X gates load the fixed auxiliary seed on exactly the newly owned wires. -/
def loadProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (after modulus.size).quantumLayout :=
  Execution.PreparationLoaded.program (before modulus.size) auxiliaryKey
    (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size)
    (EncodedBit.Word.BasisLoad.program (auxiliaryQubitLayout modulus.size) .empty
      (loadConstant modulus))

/-- Allocate exactly the existing fresh physical systems in the zero basis. -/
def zeroCircuit (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  .prepareZero (before modulus.size) auxiliaryKey (auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)

/-- Zero allocation followed by the literal X loading of the fixed source auxiliary bits. -/
def circuit (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  (zeroCircuit modulus).seq (Circuit.unitary (loadProgram modulus))

/-- Every newly prepared finite bit is the stated modulus-dependent value at its actual identity. -/
theorem preparation_bit (modulus : Nat) (index : Fin (auxiliaryWidth modulus.size)) :
    finTwoEquiv ((preparation modulus).value index) =
      fixedBit modulus (auxiliaryPhysicalIndex modulus.size index) :=
  finTwoEquiv.apply_symm_apply _

/-- The trace includes the zero allocation and every literal fixed-seed X gate. -/
theorem circuit_eventTrace (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (auxiliaryLayout modulus.size) ++
        (loadProgram modulus).eventTrace := by
  change (zeroCircuit modulus).eventTrace path.1 ++
    (Circuit.unitary (loadProgram modulus)).eventTrace path.2 = _
  rfl

variable {Reference : Register} {H : Type} [Fintype H]

/-- Actual fresh/old/reference tensor coordinates for this source allocation. -/
def joined (modulus : Nat) (fresh : (auxiliaryLayout modulus.size).register.Index)
    (old : (Register.prod (before modulus.size).register Reference).Index) :
    (Register.prod (after modulus.size).register Reference).Index :=
  prepareContextBasisEquiv (before modulus.size) Reference auxiliaryKey
    (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) (fresh, old)

/-- The literal X list maps the zero auxiliary bank to the modulus-dependent fixed seed. -/
theorem sourceLoad_seed (modulus : Nat) :
    (EncodedBit.Word.BasisLoad.program (auxiliaryQubitLayout modulus.size) .empty
      (loadConstant modulus)).applyNormalized
        (NormalizedVector.ket (BasisPreparation.zero (auxiliaryLayout modulus.size)).value) =
      NormalizedVector.ket (preparation modulus).value := by
  have zeroBasis : (auxiliaryQubitLayout modulus.size).binaryIndexEquiv.symm 0 =
      (BasisPreparation.zero (auxiliaryLayout modulus.size)).value := by
    funext index
    apply Fin.ext
    change (finTwoEquiv.symm ((0 : Nat).testBit index.rev.val)).val = 0
    simp only [Nat.zero_testBit]
    decide
  have seedBasis : (auxiliaryQubitLayout modulus.size).binaryIndexEquiv.symm
      (loadConstant modulus) = (preparation modulus).value :=
    (auxiliaryQubitLayout modulus.size).binaryIndexEquiv.symm_apply_apply _
  rw [← zeroBasis, ← seedBasis]
  exact EncodedBit.Word.BasisLoad.basisLoad_apply_zero
    (auxiliaryQubitLayout modulus.size) .empty (loadConstant modulus)

/-- Every old input label is untouched while the literal X list loads the exact fixed seed. -/
theorem loadProgram_seed (modulus : Nat)
    (old : (before modulus.size).register.Index) :
    (loadProgram modulus).applyNormalized
        (NormalizedVector.ket
          (Execution.preparedLocalBasisEquiv (before modulus.size) auxiliaryKey
            (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
            (auxiliary_disjoint modulus.size)
            ((BasisPreparation.zero (auxiliaryLayout modulus.size)).value, old))) =
      NormalizedVector.ket
        (Execution.preparedLocalBasisEquiv (before modulus.size) auxiliaryKey
          (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
          (auxiliary_disjoint modulus.size) ((preparation modulus).value, old)) := by
  exact Execution.PreparationLoaded.program_joined_ket (before modulus.size) auxiliaryKey
    (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) _ _ _ (sourceLoad_seed modulus) old

/-- Fixed auxiliary loading charges at most one actual X per newly owned wire. -/
theorem loadProgram_resources (modulus : Nat) :
    (loadProgram modulus).eventCost.card ≤ auxiliaryWidth modulus.size ∧
      (loadProgram modulus).evaluatedEventDepth (fun _ => 1) ≤
        auxiliaryWidth modulus.size := by
  have count : (loadProgram modulus).eventCost.card =
      EncodedBit.Word.BasisLoad.xCount (loadConstant modulus) := by
    calc
      _ = (EncodedBit.Word.BasisLoad.program (auxiliaryQubitLayout modulus.size) .empty
          (loadConstant modulus)).eventCost.card := by
        exact congrArg Multiset.card
          (Execution.PreparationLoaded.program_eventCost (before modulus.size) auxiliaryKey
            (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
            (auxiliary_disjoint modulus.size) _)
      _ = _ := by
        rw [EncodedBit.Word.BasisLoad.basisLoad_eventCost]
        simp [ResourcePool.singleton]
  have depth : (loadProgram modulus).evaluatedEventDepth (fun _ => 1) =
      EncodedBit.Word.BasisLoad.xCount (loadConstant modulus) := by
    exact (Execution.PreparationLoaded.program_unitDepth (before modulus.size) auxiliaryKey
      (auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
      (auxiliary_disjoint modulus.size) _).trans
        (EncodedBit.Word.BasisLoad.basisLoad_unitDepth
          (auxiliaryQubitLayout modulus.size) .empty (loadConstant modulus))
  exact ⟨count.le.trans (EncodedBit.Word.BasisLoad.basisLoad_count_le _),
    depth.le.trans (EncodedBit.Word.BasisLoad.basisLoad_count_le _)⟩

/-- The complete joint input-reference density is zero-prepared and then acted on by
the literal fixed-seed X program, with all incoming coherences retained. -/
theorem execute_full_density (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((circuit modulus).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (loadProgram modulus).matrix
          (1 : UnitaryOperator Reference))
        (((zeroCircuit modulus).execute Reference state).quantumMarginal) := by
  rw [circuit, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.unitary_jointDensity]

/-- Actual preparation preserves every external-reference matrix entry, not only diagonal mass. -/
theorem execute_reference_entry (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((circuit modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) :=
  (by
    rw [execute_full_density]
    exact (DensityOperator.localUnitary_reference_entry (loadProgram modulus).matrix
      (((zeroCircuit modulus).execute Reference state).quantumMarginal) left right).trans
        (by
          convert (Circuit.prepareZero_reference_entry (gates := AlgorithmGate.model)
              (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
              state auxiliaryKey (auxiliaryLayout modulus.size)
              (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size) left right)
            using 1; rfl))

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputPreparation
