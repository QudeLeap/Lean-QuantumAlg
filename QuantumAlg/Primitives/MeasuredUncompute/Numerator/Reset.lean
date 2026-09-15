/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.ResetMeasurement
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Actual numerator Hadamard, Z writes, and stored-result X reset

The original numerator receives the existing Hadamard layer. Its Z
outcomes are written to the actual finite result cells, whose structural
read selects the literal X reset sequence. The finite label below only
indexes this compiled gate family; no packed word is allocated or written.
Every numerator, input and EEA history wire remains live throughout
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorReset

noncomputable section

open Execution MAU.Inversion.SharedEEA

/-- A stored finite vector indexes its concrete literal X sequence in little-endian order. -/
def outcome {width : Nat} (value : CShape.Value (.fixedVector width (.finite 2))) :
    Fin (2 ^ width) :=
  ⟨Nat.ofBits (QubitReadouts.mask value), Nat.ofBits_lt_two_pow _⟩

theorem outcome_bit {width : Nat} (value : CShape.Value (.fixedVector width (.finite 2)))
    (index : Fin width) :
    (outcome value).val.testBit index.val = QubitReadouts.mask value index := by
  exact Nat.testBit_ofBits_lt (QubitReadouts.mask value) index.val index.isLt

/-- The chosen literal reset uses only the existing numerator after the complete source frame. -/
def member (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2))) :
    UnitaryCircuit (Qubits (OutputCopy.encoding width).width) :=
  UnitaryCircuit.prodRight (m := (encoding width).width) (StoredWordReset.program (outcome value))

private theorem member_within (width : Nat)
    (value : CShape.Value (.fixedVector width (.finite 2))) :
    (member width value).physical_idx ⊆ List.range (OutputCopy.encoding width).width :=
  UnitaryCircuit.prodRight_physical_idx_subset_range (StoredWordReset.program (outcome value))
    (by rw [StoredWordReset.storedWordReset_physical]; exact List.Subset.refl _)

/-- The same selected native sequence resets Y and preserves the entire remaining source label. -/
theorem member_ket (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2)))
    (frame : Fin (2 ^ (encoding width).width)) :
    (member width value).applyNormalized
      (NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
        (prodEquiv (frame, outcome value))) =
      NormalizedVector.ket (R := Qubits (OutputCopy.encoding width).width)
        (prodEquiv (frame, 0)) :=
  UnitaryCircuit.Realizes.prodRight_applyNormalized_ket_of_eq
    (StoredWordReset.program (outcome value)) frame (outcome value) 0
    (StoredWordReset.storedWordReset_ket (outcome value))

/-- Read the actual finite outcomes and execute precisely their selected X sequence. -/
def reset (width : Nat) :
    Circuit (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  NumeratorRuntime.selected width (member width) (member_within width)

/-- The native Hadamard layer acts only on the original numerator word. -/
def hadamardMember (width : Nat) : UnitaryCircuit (Qubits (OutputCopy.encoding width).width) :=
  UnitaryCircuit.prodRight (m := (encoding width).width) (WalshHadamard.hadamardLayer width)

private theorem hadamard_within (width : Nat) :
    (hadamardMember width).physical_idx ⊆ List.range (OutputCopy.encoding width).width :=
  UnitaryCircuit.prodRight_physical_idx_subset_range (WalshHadamard.hadamardLayer width)
    (by rw [WalshHadamard.hadamardLayer_physical_idx]; exact List.Subset.refl _)

/-- Execute that same Hadamard layer in the actual shared runtime context. -/
def hadamard (width : Nat) :
    Circuit (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  NumeratorRuntime.code width (hadamardMember width) (hadamard_within width)

/-- Actual H gates, actual Z writes, then a branch reading those same stored finite results. -/
def code (width : Nat) :
    Circuit (NumeratorMeasurement.context width) (NumeratorMeasurement.context width) :=
  .seq (hadamard width) (.seq (NumeratorMeasurement.measure width) (reset width))

/-- Each selected reset charges exactly its concrete X gate multiplicity. -/
theorem reset_cost (width : Nat) (path : (reset width).Path) :
    (reset width).resourcePool path =
      EncodedBit.Word.BasisLoad.xCount (outcome path.1) •
        ResourcePool.singleton (.gate (.builtin "x")) := by
  change ResourcePool.ofList (NumeratorRuntime.program width (member width path.1)).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, NumeratorRuntime.program_cost]
  have same : (member width path.1).eventCost =
      (StoredWordReset.program (outcome path.1)).eventCost :=
    UnitaryCircuit.prodRight_eventCost _
  exact same.trans (StoredWordReset.storedWordReset_events (outcome path.1))

/-- Its independent allowance contains at most one X correction per existing numerator bit. -/
theorem reset_budget (width : Nat) (path : (reset width).Path) :
    (reset width).resourcePool path ≤ width • ResourcePool.singleton (.gate (.builtin "x")) := by
  rw [reset_cost]
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [ResourcePool.count_nsmul, ResourcePool.count_nsmul]
  exact Nat.mul_le_mul_right _ (EncodedBit.Word.BasisLoad.basisLoad_count_le (outcome path.1))

end

end QuantumAlg.MeasuredUncompute.NumeratorReset
