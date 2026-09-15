/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Pivot.Word
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Complement
import all QuantumAlg.Components.Encoded.BitGates.Control

/-!
# Actual coherently controlled bi-flip

The body executes the proved HRS negative offset and then a literal target
complement, implementing `not (x - pivot)` [G17, paper.tex:276-277]. Its
single borrowed bit is restored on every input. Adding the existing
leading coherent control preserves the exact phase and uses the original
flag/word/helper layout. Native controlled gate coordinates are retained
by the actual Core control transform.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open Nat.FixedWidth

/-- The finite arithmetic action agrees with the complement of the compiled negative offset. -/
theorem gidneyBiFlipWord_eq_offset_complement (width : Nat)
    (pivot : Fin (2 ^ width + 1)) (input : Fin (2 ^ width)) :
    HRS.complementWord (HRS.addWord (negatedPivot width pivot.val) input) =
      biFlipWordOutput pivot input := by
  apply Fin.ext
  exact (Nat.FixedWidth.biFlip_eq_complement_sub_mod
    (by have := pivot.isLt; omega) input.isLt).symm

/-- The actual two-block body operates on the target and its one borrowed bit. -/
def biFlipBodyProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (HRS.oneDirtyEncoding width).width) :=
  (HRS.oneDirtyProgram width (negatedPivot width pivot.val)).seq
    (UnitaryCircuit.prodLeft (n := 1) (complementProgram width))

/-- Independent body action, with the helper returned exactly. -/
def biFlipBodyOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : HRS.OneDirtyRegisters width) : HRS.OneDirtyRegisters width :=
  (biFlipWordOutput pivot state.1, state.2)

theorem gidneyBiFlipBody_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (HRS.oneDirtyEncoding width) (biFlipBodyProgram width pivot)
      (biFlipBodyOutput pivot) := by
  have h := (HRS.hrsOneDirty_realizes width (negatedPivot width pivot.val)).seq
    ((gidneyComplement_realizes width).prodLeft (right := BinaryLabelEncoding.bool))
  apply h.congrStep
  rintro ⟨input, helper⟩
  exact congrArg (fun word => (word, helper))
    (gidneyBiFlipWord_eq_offset_complement width pivot input)

/-- Coherent flag control of the actual negative-offset/complement body. -/
def biFlipProgram (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  UnitaryCircuit.controlLeading (biFlipBodyProgram width pivot)

/-- The original flag is preserved and determines whether the finite bi-flip is applied. -/
def biFlipOutput {width : Nat} (pivot : Fin (2 ^ width + 1))
    (state : Registers width) : Registers width :=
  (state.1, (if state.1 then biFlipWordOutput pivot state.2.1 else state.2.1, state.2.2))

theorem gidneyBiFlip_realizes (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (biFlipProgram width pivot)
      (biFlipOutput pivot) := by
  have hshift : UnitaryCircuit.Realizes (HRS.oneDirtyEncoding width)
      (UnitaryCircuit.shiftPhysicalIdx 1 (biFlipBodyProgram width pivot))
      (biFlipBodyOutput pivot) := by
    refine ⟨?_⟩
    intro input
    rw [UnitaryCircuit.shiftPhysicalIdx_applyNormalized]
    exact (gidneyBiFlipBody_realizes width pivot).apply_encoded_ket input
  have hcontrol := hshift.controlOnTrue [0]
    (UnitaryCircuit.leadingControlLayout (biFlipBodyProgram width pivot))
  apply hcontrol.congrStep
  rintro ⟨flag, input, helper⟩
  cases flag <;> rfl

private theorem biFlipBody_range (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipBodyProgram width pivot).physical_idx ⊆ List.range (width + 1) := by
  have hadd : (HRS.oneDirtyProgram width (negatedPivot width pivot.val)).physical_idx ⊆
      List.range (width + 1) := by
    rw [HRS.hrsOneDirty_physical]
    exact fun _ h => h
  have hcomplement := UnitaryCircuit.prodLeft_physical_idx_subset_range
    (n := 1) (complementProgram width)
    (EncodedBit.GateSpec.programList_physical_idx_subset_range (complementGates width))
  exact UnitaryCircuit.seq_physical_idx_subset _ _ hadd hcomplement

/-- All actual gates stay in the original word and the two declared arbitrary bits. -/
theorem gidneyBiFlip_physical_range (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).physical_idx ⊆ List.range (width + 2) := by
  have h := UnitaryCircuit.controlLeading_physical_idx_subset_range
    (biFlipBodyProgram width pivot) (biFlipBody_range width pivot)
  have hwidth : 1 + (HRS.oneDirtyEncoding width).width = width + 2 := by
    change 1 + (width + 1) = width + 2
    omega
  unfold biFlipProgram
  simpa only [hwidth] using h

/-- The actual body ledger is the HRS negative-offset ledger plus the literal X ledger. -/
theorem gidneyBiFlipBody_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipBodyProgram width pivot).eventCost =
      (HRS.oneDirtyProgram width (negatedPivot width pivot.val)).eventCost +
        (complementProgram width).eventCost := by
  exact (UnitaryCircuit.seq_eventCost (R := Qubits (width + 1))
    (HRS.oneDirtyProgram width (negatedPivot width pivot.val))
    (UnitaryCircuit.prodLeft (m := width) (n := 1) (complementProgram width))).trans
      (congrArg (fun pool : ResourcePool .quantum =>
        (HRS.oneDirtyProgram width (negatedPivot width pivot.val)).eventCost + pool)
        (UnitaryCircuit.prodLeft_eventCost (m := width) (n := 1) (complementProgram width)))

/-- Every body event receives its real additional quantum-control coordinate. -/
theorem gidneyBiFlip_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (biFlipProgram width pivot).eventCost = ResourcePool.controlForDimension 2
      ((HRS.oneDirtyProgram width (negatedPivot width pivot.val)).eventCost +
        (complementProgram width).eventCost) := by
  exact (UnitaryCircuit.controlLeading_eventCost (n := width + 1)
    (biFlipBodyProgram width pivot)).trans
      (congrArg (fun pool : ResourcePool .quantum => ResourcePool.controlForDimension 2 pool)
        (gidneyBiFlipBody_eventCost width pivot))

end

end QuantumAlg.MAU.Addition.Gidney
