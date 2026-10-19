/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction.Matrix
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Components.Encoded.BitGates.Realization
import Mathlib.Algebra.BigOperators.Fin

/-!
# One actual parallel numerator correction layer

The stored little-endian word selects native X gates at its original
big-endian physical positions. Every selected bit remains charged, but
the disjoint one-wire circuits execute simultaneously. This member adds
no storage and retains the exact zero column, including its phase.
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorResetParallel

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ZReset.BankParallel
open scoped BigOperators

/-- Convert the stored little-endian label to the original physical wire order. -/
def selected {width : Nat} (value : Fin (2 ^ width)) (index : Fin width) : Bool :=
  value.val.testBit index.rev.val

/-- The real selected X gates act in parallel on the existing numerator bank. -/
def program {width : Nat} (value : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical width).toQuantum :=
  Correction.layer .empty width (selected value)

private lemma selected_basis {width : Nat} (value : Fin (2 ^ width)) :
    selected value = fun index =>
      decide ((((QubitLayout.canonical width).basisEquiv.symm value) index).val = 1) := by
  funext index
  change value.val.testBit index.rev.val =
    decide ((finTwoEquiv.symm (value.val.testBit index.rev.val)).val = 1)
  cases value.val.testBit index.rev.val <;> rfl

private lemma zero_basis (width : Nat) :
    (QubitLayout.canonical width).basisEquiv.symm 0 =
      (Gate.HadamardLayer.layout width).zeroLabel := by
  funext index
  change finTwoEquiv.symm ((0 : Fin (2 ^ width)).val.testBit index.rev.val) = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- The actual parallel member resets its measured word with exact phase. -/
lemma program_ket {width : Nat} (value : Fin (2 ^ width)) :
    ((program value).applyNormalized environment)
      (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm value)) =
        NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm 0) := by
  apply NormalizedVector.ext
  intro row
  change ((program value).matrix environment).applyVec
      (NormalizedVector.ket ((QubitLayout.canonical width).basisEquiv.symm value)) row = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  change ((Correction.layer .empty width (selected value)).matrix environment) row
      ((QubitLayout.canonical width).basisEquiv.symm value) = _
  rw [selected_basis, Correction.layer_reset_column,
    zero_basis, NormalizedVector.ket_apply]

/-- Canonical binary labels expose the same complete phase-preserving reset column. -/
lemma program_binary_ket {width : Nat} (value : Fin (2 ^ width)) :
    ((program value).binaryMatrix environment).apply (NormalizedVector.ket (R := Qubits width)
      value) =
      NormalizedVector.ket (R := Qubits width) 0 :=
  UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    (program value) value 0 (program_ket value)

private lemma correction_count_sum (width : Nat) (mask : Fin width → Bool) :
    Correction.xCount width mask = ∑ index, if mask index then 1 else 0 := by
  induction width with
  | zero => simp [Correction.xCount]
  | succ width ih =>
      rw [Correction.xCount, ih, Fin.sum_univ_castSucc]

private lemma source_count_sum {width : Nat} (value : Fin (2 ^ width)) :
    EncodedBit.Word.BasisLoad.xCount value =
      ∑ index : Fin width, if value.val.testBit index.val then 1 else 0 := by
  have filtered (indices : List (Fin width)) :
      (indices.filter (fun index => value.val.testBit index.val)).length =
        (indices.map (fun index => if value.val.testBit index.val then 1 else 0)).sum := by
    induction indices with
    | nil => rfl
    | cons index rest ih =>
        cases bit : value.val.testBit index.val <;> simp [bit, ih, Nat.add_comm]
  change ((List.ofFn fun index : Fin width => index).filter
    (fun index => value.val.testBit index.val)).length = _
  rw [filtered, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Reordering the physical positions preserves the exact original set-bit count. -/
lemma selected_count {width : Nat} (value : Fin (2 ^ width)) :
    Correction.xCount width (selected value) = EncodedBit.Word.BasisLoad.xCount value := by
  rw [correction_count_sum, source_count_sum]
  exact Equiv.sum_comp (Fin.revPerm (n := width))
    (fun index : Fin width => if value.val.testBit index.val then 1 else 0)

/-- Each and only each original selected X remains in the native ledger. -/
lemma program_eventCost {width : Nat} (value : Fin (2 ^ width)) :
    (program value).eventCost = EncodedBit.Word.BasisLoad.xCount value •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) := by
  change (Correction.layer .empty width (selected value)).eventCost = _
  rw [Correction.layer_eventCost, selected_count]

/-- An empty word takes zero time, and every nonempty word uses at most one native layer. -/
lemma program_unitDepth {width : Nat} (value : Fin (2 ^ width)) :
    (program value).evaluatedEventDepth (fun _ => 1) ≤ if width = 0 then 0 else 1 := by
  by_cases empty : width = 0
  · subst width
    simp only [if_true]
    exact le_rfl
  · rw [if_neg empty]
    exact Correction.layer_unitDepth_le .empty width (selected value)

end

end QuantumAlg.MeasuredUncompute.NumeratorResetParallel
