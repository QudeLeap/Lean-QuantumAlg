/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.PreparedFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Copy
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Prepared.BasisSupport

/-!
# Actual inverse input, XOR output, and fixed auxiliary preparation

The supplied quantum layout contains the original n-bit input and an
arbitrary n-bit XOR output on their real physical identities. Preparation
allocates exactly the existing shared-EEA complement of the input, using
the same modulus-dependent fixed basis values as the actual source
initialization [LYL+26, sec_EEA/sub_4phase.tex:104-117]. The output is
part of the live owned context, never an uncharged external reference.

All systems remain live after preparation. The complete native inverse
returns its work to these fixed preparation values; the final output
must retain and list those systems. No input label determines a fresh
preparation parameter or an initial clean-value premise.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InversePreparation

noncomputable section

open Execution

/-- Supplied input positions keep their original Work2 identities; output follows the full frame. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < width then InputPreparation.prefixWidth width + index
  else (SharedEEA.encoding width).width + (index - width)

private theorem physicalIndex_injective (width : Nat) :
    Function.Injective (fun index : Fin (width + width) => physicalIndex width index.val) := by
  intro left right same
  apply Fin.ext
  change physicalIndex width left.val = physicalIndex width right.val at same
  have leftBound := left.isLt
  have rightBound := right.isLt
  have complete := InputPreparation.complete_width width
  unfold InputPreparation.auxiliaryWidth InputPreparation.suffixWidth at complete
  unfold physicalIndex at same
  split at same <;> split at same <;> omega

/-- Exactly the original input and actual XOR target, with no caller-supplied EEA workspace. -/
def inputQubitLayout (width : Nat) : QubitLayout (width + width) where
  physical_idx index := physicalIndex width index.val
  physical_idx_injective := physicalIndex_injective width

/-- Each supplied input and target system is explicitly dimension two. -/
def inputLayout (width : Nat) : QuantumLayout (width + width) :=
  (inputQubitLayout width).toQuantumLayout

/-- One supplied owned layout contains both the input and its arbitrary XOR target. -/
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

/-- Read the actual two supplied word segments through their precise binary wire labels. -/
def inputBasisEquiv (width : Nat) :
    (before width).register.Index ≃ (Fin (2 ^ width) × Fin (2 ^ width)) :=
  (basisOfEqualWires (inputLayout width) (before width).quantumLayout
    (input_wires width)).symm.trans
      ((inputQubitLayout width).binaryIndexEquiv.trans (prodEquiv (m := width) (n := width)).symm)

/-- The existing source auxiliary allocation retains a distinct storage identity. -/
def auxiliaryKey : StorageKey := ⟨1⟩

theorem auxiliary_fresh (width : Nat) : auxiliaryKey ∉ (before width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- Every new auxiliary wire is disjoint from both the actual input and the actual output. -/
theorem auxiliary_disjoint (width : Nat) :
    List.Disjoint (InputPreparation.auxiliaryLayout width).identities
      (before width).physicalIdx := by
  rw [before_physical]
  apply List.disjoint_left.mpr
  intro wire fresh old
  change wire ∈ List.ofFn (InputPreparation.auxiliaryPhysicalIndex width) at fresh
  change wire ∈ List.ofFn
    (fun index : Fin (width + width) => physicalIndex width index.val) at old
  obtain ⟨newIndex, newPosition⟩ := List.mem_ofFn.mp fresh
  obtain ⟨oldIndex, oldPosition⟩ := List.mem_ofFn.mp old
  have newBound := newIndex.isLt
  have oldBound := oldIndex.isLt
  have complete := InputPreparation.complete_width width
  have freshBound := (InputAssembly.auxiliaryPosition width newIndex).isLt
  change InputPreparation.auxiliaryPhysicalIndex width newIndex <
    (SharedEEA.encoding width).width at freshBound
  unfold physicalIndex at oldPosition
  split at oldPosition
  · unfold InputPreparation.auxiliaryPhysicalIndex at newPosition
    split at newPosition <;> omega
  · omega

/-- The actual post-context owns all new auxiliary systems and the unchanged input/output pair. -/
def after (width : Nat) : RuntimeCtx .quantum :=
  (before width).addOwnedLayout auxiliaryKey (InputPreparation.auxiliaryLayout width)
    (auxiliary_fresh width) (auxiliary_disjoint width)

/-- Literal X loading of the source's fixed auxiliary bits beside both supplied words. -/
def loadProgram (modulus : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (after modulus.size).quantumLayout :=
  Execution.PreparationLoaded.program (before modulus.size) auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size)
    (EncodedBit.Word.BasisLoad.program (InputPreparation.auxiliaryQubitLayout modulus.size)
      .empty (InputPreparation.loadConstant modulus))

/-- The same physical auxiliary bank is first allocated in zero. -/
def zeroCircuit (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  .prepareZero (before modulus.size) auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)

/-- Prepare the fixed source basis by zero allocation and real X gates. -/
def circuit (modulus : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before modulus.size) (after modulus.size) :=
  (zeroCircuit modulus).seq (Circuit.unitary (loadProgram modulus))

/-- Exact actual fresh/old wire assembly, preserving both original quantum word segments. -/
def assembly (width : Nat) :
    ((InputPreparation.auxiliaryLayout width).register.Index × (before width).register.Index) ≃
      (after width).register.Index :=
  preparedLocalBasisEquiv (before width) auxiliaryKey (InputPreparation.auxiliaryLayout width)
    (auxiliary_fresh width) (auxiliary_disjoint width)

/-- No additional hidden system accompanies the new target word or the existing auxiliary layout. -/
theorem total_width (width : Nat) :
    InputPreparation.auxiliaryWidth width + (width + width) =
      (OutputCopy.encoding width).width := by
  change InputPreparation.auxiliaryWidth width + (width + width) =
    (SharedEEA.encoding width).width + width
  have complete := InputPreparation.complete_width width
  omega

/-- The trace charges zero allocation and every fixed-seed X gate. -/
theorem circuit_eventTrace (modulus : Nat) (path : (circuit modulus).Path) :
    (circuit modulus).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
          (loadProgram modulus).eventTrace := by
  change (zeroCircuit modulus).eventTrace path.1 ++
    (Circuit.unitary (loadProgram modulus)).eventTrace path.2 = _
  rfl

/-- Both supplied words retain their arbitrary old values while real X gates load the seed. -/
theorem loadProgram_seed (modulus : Nat) (old : (before modulus.size).register.Index) :
    (loadProgram modulus).applyNormalized
        (NormalizedVector.ket
          (assembly modulus.size
            ((BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size)).value, old))) =
      NormalizedVector.ket
        (assembly modulus.size ((InputPreparation.preparation modulus).value, old)) :=
  Execution.PreparationLoaded.program_joined_ket (before modulus.size) auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size) _ _ _ (InputPreparation.sourceLoad_seed modulus) old

/-- The XOR interface's fixed auxiliary loading has the same independent wire-count cap. -/
theorem loadProgram_resources (modulus : Nat) :
    (loadProgram modulus).eventCost.card ≤ InputPreparation.auxiliaryWidth modulus.size ∧
      (loadProgram modulus).evaluatedEventDepth (fun _ => 1) ≤
        InputPreparation.auxiliaryWidth modulus.size := by
  have count : (loadProgram modulus).eventCost.card =
      EncodedBit.Word.BasisLoad.xCount (InputPreparation.loadConstant modulus) := by
    calc
      _ = (EncodedBit.Word.BasisLoad.program
          (InputPreparation.auxiliaryQubitLayout modulus.size) .empty
          (InputPreparation.loadConstant modulus)).eventCost.card := by
        exact congrArg Multiset.card
          (Execution.PreparationLoaded.program_eventCost (before modulus.size) auxiliaryKey
            (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
            (auxiliary_disjoint modulus.size) _)
      _ = _ := by
        rw [EncodedBit.Word.BasisLoad.basisLoad_eventCost]
        simp [ResourcePool.singleton]
  have depth : (loadProgram modulus).evaluatedEventDepth (fun _ => 1) =
      EncodedBit.Word.BasisLoad.xCount (InputPreparation.loadConstant modulus) := by
    exact (Execution.PreparationLoaded.program_unitDepth (before modulus.size) auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
      (auxiliary_disjoint modulus.size) _).trans
        (EncodedBit.Word.BasisLoad.basisLoad_unitDepth
          (InputPreparation.auxiliaryQubitLayout modulus.size) .empty
          (InputPreparation.loadConstant modulus))
  exact ⟨count.le.trans (EncodedBit.Word.BasisLoad.basisLoad_count_le _),
    depth.le.trans (EncodedBit.Word.BasisLoad.basisLoad_count_le _)⟩

variable {Reference : Register} {H : Type} [Fintype H]

/-- The actual zero allocation and fixed X list preserve every old joint coherence. -/
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

/-- The actual zero allocation and X gates realize the independent fixed-seed tensor. -/
theorem execute_preparedDensity (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((circuit modulus).execute Reference state).quantumMarginal =
      preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
        (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
        (InputPreparation.preparation modulus).normalized Reference state.quantumMarginal := by
  rw [execute_full_density]
  have zero : ((zeroCircuit modulus).execute Reference state).quantumMarginal =
      preparedDensity auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
        (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
        (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size)).normalized
        Reference state.quantumMarginal := by
    change ((state.prepare auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
      (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size)
      (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size))).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))).quantumMarginal = _
    rw [State.mapHistory_quantumMarginal, State.prepare_quantumMarginal,
      prepareContext_quantumMarginal_eq_preparedDensity]
  rw [zero]
  exact preparedDensity_load_ket auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size) (auxiliary_fresh modulus.size)
    (auxiliary_disjoint modulus.size)
    (BasisPreparation.zero (InputPreparation.auxiliaryLayout modulus.size)).value
    (InputPreparation.preparation modulus).value
    (loadProgram modulus).matrix (loadProgram_seed modulus) state.quantumMarginal

/-- Fixed auxiliary loading leaves the complete external-reference matrix unchanged. -/
theorem execute_reference_entry (modulus : Nat)
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) (left right : Reference.Index) :
    (∑ basis : (after modulus.size).register.Index,
      ((circuit modulus).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) := by
  rw [execute_full_density]
  exact (DensityOperator.localUnitary_reference_entry (loadProgram modulus).matrix
    (((zeroCircuit modulus).execute Reference state).quantumMarginal) left right).trans
      (by
        convert (Circuit.prepareZero_reference_entry (gates := AlgorithmGate.model)
          (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
          state auxiliaryKey (InputPreparation.auxiliaryLayout modulus.size)
          (auxiliary_fresh modulus.size) (auxiliary_disjoint modulus.size) left right)
          using 1; rfl)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InversePreparation
