/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Layout
import all QuantumAlg.Components.Encoded.BitGates.Control
import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection

/-!
# Native active arithmetic and inactive preservation

The active branch uses the existing prime-field measured multiplication or
division components. The inactive branch copies Y into the existing A before
measurement and corrects A from the same actual stored mask. This retains
the three-word frame while protecting arbitrary inactive input words.
The external coherent-control construction extends the source's measured
arithmetic [LYL+26, sec_point_add/sec_point_add.tex:52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA

private def controlIdentity (width : Nat) : UnitaryCircuit (Qubits 1) :=
  .identity (Qubits 1) [controlWire width] (by simp)

private theorem controlMerge (width : Nat)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    PhysicalLayout.DisjointMerge [controlWire width] body.physical_idx := by
  refine ⟨by simp, body.physical_idx_nodup, ?_⟩
  apply List.disjoint_left.mpr
  intro wire control original
  have same : wire = controlWire width := List.mem_singleton.mp control
  have bound := List.mem_range.mp (within original)
  rw [same] at bound
  exact (Nat.lt_irrefl (frameWidth width)) bound

/-- A real quantum control at its disjoint owned address, with actual controlled events. -/
def controlled (width : Nat) (active : Fin 2)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    UnitaryCircuit (Qubits (1 + frameWidth width)) :=
  .controlQubitsAt [controlWire width] body (controlMerge width body within) active

theorem controlled_within (width : Nat) (active : Fin 2)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    (controlled width active body within).physical_idx ⊆ List.range (1 + frameWidth width) := by
  apply UnitaryCircuit.controlQubitsAt_physical_idx_subset
  · intro wire present
    have same := List.mem_singleton.mp present
    rw [same]
    exact List.mem_range.mpr (by unfold controlWire; omega)
  · intro wire present
    have bound := List.mem_range.mp (within present)
    exact List.mem_range.mpr (by omega)

theorem controlled_trace (width : Nat) (active : Fin 2)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    (controlled width active body within).eventTrace =
      body.eventTrace.map (fun event => event.controlForDimension 2) := by
  exact UnitaryCircuit.controlQubitsAt_eventTrace _ _ _ _

theorem controlled_cost (width : Nat) (active : Fin 2)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    (controlled width active body within).eventCost =
      ResourcePool.controlForDimension 2 body.eventCost :=
  UnitaryCircuit.controlQubitsAt_eventCost _ _ _ _

/-- Exact native columns keep every cross-control block, including inactive identity columns. -/
theorem controlled_matrix (width : Nat) (active : Fin 2)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width))
    (rowControl columnControl : Fin 2) (row column : Fin (2 ^ frameWidth width)) :
    (controlled width active body within).matrix
      (prodEquiv (rowControl, row)) (prodEquiv (columnControl, column)) =
      if rowControl = columnControl then
        if rowControl = active then body.matrix row column
        else if row = column then 1 else 0
      else 0 := by
  rw [controlled, UnitaryCircuit.controlQubitsAt_matrix]
  change UnitaryOperator.controlled (Qubits 1) active body.matrix
    ((prodEquiv (m := 1) (n := frameWidth width)).symm (prodEquiv (rowControl, row)))
    ((prodEquiv (m := 1) (n := frameWidth width)).symm (prodEquiv (columnControl, column))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact UnitaryOperator.controlled_apply _ _ _ _ _

/-- Extend an unconditional native member by the actual resident control identity. -/
def uncontrolled (width : Nat)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    UnitaryCircuit (Qubits (1 + frameWidth width)) :=
  .reindex prodEquiv (.tensor (controlIdentity width) body (controlMerge width body within))

theorem uncontrolled_within (width : Nat)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    (uncontrolled width body within).physical_idx ⊆ List.range (1 + frameWidth width) := by
  intro wire present
  change wire ∈ [controlWire width] ++ body.physical_idx at present
  rcases List.mem_append.mp present with control | original
  · have same := List.mem_singleton.mp control
    rw [same]
    exact List.mem_range.mpr (by unfold controlWire; omega)
  · have bound := List.mem_range.mp (within original)
    exact List.mem_range.mpr (by omega)

theorem uncontrolled_trace (width : Nat)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (within : body.physical_idx ⊆ List.range (frameWidth width)) :
    (uncontrolled width body within).eventTrace = body.eventTrace := rfl

private theorem complete_within (width : Nat)
    (body : UnitaryCircuit (Qubits (frameWidth width)))
    (complete : body.physical_idx = List.range (frameWidth width)) :
    body.physical_idx ⊆ List.range (frameWidth width) := by
  rw [complete]
  exact List.Subset.refl _

/-- Save inactive Y in the already clean A with literal native CNOT gates. -/
def copy (width : Nat) : UnitaryCircuit (Qubits (frameWidth width)) :=
  EncodedBit.Word.xorIntoProgram (FramePorts.numerator width) (FramePorts.accumulator width)
    (fun index => (FramePorts.accumulator_numerator_ne width index index).symm)

theorem copy_within (width : Nat) :
    (copy width).physical_idx ⊆ List.range (frameWidth width) :=
  EncodedBit.Word.xorIntoProgram_physical_idx_subset_range _ _ _

/-- Read A in the exact little-endian order of the actual finite measurement cells. -/
def inactiveWord (width : Nat) : EncodedBit.Word (OutputCopy.encoding width) width :=
  ⟨fun index => (FramePorts.accumulator width).bit index.rev⟩

/-- The same actual stored result selects the corresponding reversed physical A addresses. -/
def inactiveMask (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2))) :
    UnitaryCircuit (Qubits (frameWidth width)) :=
  EncodedBit.Word.PhaseCorrection.program (inactiveWord width) (QubitReadouts.mask value)

theorem inactiveMask_within (width : Nat)
    (value : CShape.Value (.fixedVector width (.finite 2))) :
    (inactiveMask width value).physical_idx ⊆ List.range (frameWidth width) :=
  complete_within width _ (EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_physical _ _)

/-- The existing product and the inactive copy use disjoint quantum-control sectors. -/
def save (modulus : Nat) : UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  .seq (controlled modulus.size 1
    (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus))
    (ReusedProduct.original_within modulus.size (InPlaceArithmetic.modulusWord modulus)))
    (controlled modulus.size 0 (copy modulus.size) (copy_within modulus.size))

theorem save_within (modulus : Nat) :
    (save modulus).physical_idx ⊆ List.range (1 + frameWidth modulus.size) :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (controlled_within _ _ _ _)
    (controlled_within _ _ _ _)

/-- The original forward EEA is active only on the caller's quantum control. -/
def forward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  controlled modulus.size 1 (NativeEEAFrame.forward modulus prime)
    (complete_within modulus.size _ (NativeEEAFrame.forward_physical modulus prime))

def reusedForward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  controlled modulus.size 1 (NativeReusedEEA.forward modulus prime)
    (complete_within modulus.size _ (NativeReusedEEA.forward_physical modulus prime))

/-- The identical inverse EEA retains the same quantum control and the same restored history. -/
def backward (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  controlled modulus.size 1 (NativeEEAFrame.backward modulus prime)
    (complete_within modulus.size _ (NativeEEAFrame.backward_physical modulus prime))

/-- Both quantum sectors cancel their measurement phase using the actual same stored vector. -/
def correction (modulus : Nat)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  .seq (controlled modulus.size 1
    (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus) value)
    (NumeratorCorrection.member_within modulus.size
      (InPlaceArithmetic.modulusWord modulus) value))
    (controlled modulus.size 0 (inactiveMask modulus.size value) (inactiveMask_within _ _))

/-- Unconditional final native exchange restores A and returns the selected result to Y. -/
def swap (width : Nat) : UnitaryCircuit (Qubits (1 + frameWidth width)) :=
  uncontrolled width (FrameSwap.program width)
    (complete_within width _ (FrameSwap.frameSwap_physical width))

/-- The exact native prefix preceding the real H/Z/reset instructions. -/
def beforeReset (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus) :
    UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  match operation with
  | .division => .seq (forward modulus prime) (save modulus)
  | .multiplication => save modulus

/-- The exact native suffix selected by the actual stored outcome after reset. -/
def suffix (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    UnitaryCircuit (Qubits (1 + frameWidth modulus.size)) :=
  match operation with
  | .division => .seq (backward modulus prime) (.seq (correction modulus value) (swap modulus.size))
  | .multiplication => .seq (reusedForward modulus prime)
      (.seq (correction modulus value) (.seq (backward modulus prime) (swap modulus.size)))

theorem beforeReset_within (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) :
    (beforeReset operation modulus prime).physical_idx ⊆ List.range (1 + frameWidth
      modulus.size) := by
  cases operation
  · exact save_within modulus
  · exact UnitaryCircuit.seq_physical_idx_subset _ _ (controlled_within _ _ _ _) (save_within _)

theorem correction_within (modulus : Nat)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (correction modulus value).physical_idx ⊆ List.range (1 + frameWidth modulus.size) :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (controlled_within _ _ _ _)
    (controlled_within _ _ _ _)

theorem suffix_within (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (suffix operation modulus prime value).physical_idx ⊆
      List.range (1 + frameWidth modulus.size) := by
  cases operation
  · exact UnitaryCircuit.seq_physical_idx_subset _ _ (controlled_within _ _ _ _)
      (UnitaryCircuit.seq_physical_idx_subset _ _ (correction_within _ _)
        (UnitaryCircuit.seq_physical_idx_subset _ _ (controlled_within _ _ _ _)
          (uncontrolled_within _ _ _)))
  · exact UnitaryCircuit.seq_physical_idx_subset _ _ (controlled_within _ _ _ _)
      (UnitaryCircuit.seq_physical_idx_subset _ _ (correction_within _ _)
        (uncontrolled_within _ _ _))

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
