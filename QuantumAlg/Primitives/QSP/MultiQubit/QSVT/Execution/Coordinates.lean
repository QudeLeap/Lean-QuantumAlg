/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Counts
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Resources
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Counts
import all QuantumAlg.Components.GateModel.Algorithm

/-!
# Separate native gate bounds for Hermitian polynomial transformations

The bounds classify the exact pool of the same expanded word. Each source
Toffoli contributes its six CNOTs and nine single-qubit gates. All original
block and signal widths, including zero, remain in the construction.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution

noncomputable section

open Gate.Toffoli

@[simp] private lemma single_ne_cnot :
    AlgorithmGate.Coordinate.singleQubit ≠ AlgorithmGate.Coordinate.cnot := by decide

@[simp] private lemma single_ne_toffoli :
    AlgorithmGate.Coordinate.singleQubit ≠ AlgorithmGate.Coordinate.toffoli := by decide

@[simp] private lemma cnot_ne_single :
    AlgorithmGate.Coordinate.cnot ≠ AlgorithmGate.Coordinate.singleQubit := by decide

@[simp] private lemma cnot_ne_toffoli :
    AlgorithmGate.Coordinate.cnot ≠ AlgorithmGate.Coordinate.toffoli := by decide

private lemma positive_conjunction_bound (m : Nat) (positive : 0 < m) :
    EncodedBit.Word.OneDirtyLayout.gateCount m ≤ 8 * m := by
  by_cases large : 5 ≤ m
  · rw [EncodedBit.Word.OneDirtyLayout.gateCount_of_five_le large]
    omega
  · interval_cases m <;> norm_num [EncodedBit.Word.OneDirtyLayout.gateCount]

private lemma sourceWork_coordinate_bounds (oracles : OracleModel) (m : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (ZeroProjector.SourceWork.budget oracles m) +
        6 * ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (ZeroProjector.SourceWork.budget oracles m) ≤ 48 * m ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (ZeroProjector.SourceWork.budget oracles m) +
        9 * ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (ZeroProjector.SourceWork.budget oracles m) ≤ 74 * m + 1 := by
  by_cases zero : m = 0
  · subst m
    simp [reduceCtorEq, ZeroProjector.SourceWork.budget]
  by_cases one : m = 1
  · subst m
    simp [reduceCtorEq, ZeroProjector.SourceWork.budget]
  have conjunction := positive_conjunction_bound m (by omega)
  simp [reduceCtorEq, ZeroProjector.SourceWork.budget, zero, one]
  omega

private lemma realPhase_coordinate_bounds (oracles : OracleModel) (m n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (KnownZero.Total.phaseBudget m n oracles) +
        6 * ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (KnownZero.Total.phaseBudget m n oracles) ≤ 192 * m ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (KnownZero.Total.phaseBudget m n oracles) +
        9 * ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (KnownZero.Total.phaseBudget m n oracles) ≤ 296 * m + 3 := by
  cases n with
  | zero =>
      cases m with
      | zero => simp [reduceCtorEq, KnownZero.Total.phaseBudget]
      | succ m =>
          obtain ⟨cnot, single⟩ := sourceWork_coordinate_bounds oracles m
          simp [reduceCtorEq, KnownZero.Total.phaseBudget]
          constructor <;> omega
  | succ n =>
      obtain ⟨cnot, single⟩ := sourceWork_coordinate_bounds oracles m
      simp [reduceCtorEq, KnownZero.Total.phaseBudget]
      constructor <;> omega

private lemma complexPhase_coordinate_bounds (oracles : OracleModel) (m n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
        (KnownZero.Total.Four.nativePhaseBudget m n oracles) +
        6 * ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (KnownZero.Total.Four.nativePhaseBudget m n oracles) ≤ 192 * m + 6 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
        (KnownZero.Total.Four.nativePhaseBudget m n oracles) +
        9 * ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
          (KnownZero.Total.Four.nativePhaseBudget m n oracles) ≤ 296 * m + 6 := by
  cases n with
  | zero =>
      cases m with
      | zero => simp [reduceCtorEq, KnownZero.Total.Four.nativePhaseBudget]
      | succ m =>
          obtain ⟨cnot, single⟩ := sourceWork_coordinate_bounds oracles m
          simp [reduceCtorEq, KnownZero.Total.Four.nativePhaseBudget]
          constructor <;> omega
  | succ n =>
      obtain ⟨cnot, single⟩ := sourceWork_coordinate_bounds oracles m
      simp [reduceCtorEq, KnownZero.Total.Four.nativePhaseBudget]
      constructor <;> omega

/-- Separate CNOT and single-qubit ceilings of the exact real-parity execution pool. -/
lemma realBudget_coordinate_bounds (m n L : Nat) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .cnot) (realBudget m n L) ≤ 192 * m * L ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
        (.gate .singleQubit) (realBudget m n L) ≤ (296 * m + 3) * L + 2 := by
  by_cases zero : L = 0
  · subst L
    simp [realBudget, reduceCtorEq]
  obtain ⟨cnot, single⟩ :=
    realPhase_coordinate_bounds (UnitarySource.model (m + n) false true false) m n
  simp [reduceCtorEq, realBudget, zero, expanded_native_count, replacementCount,
    KnownZero.Total.budget, KnownZero.Total.eventPool]
  constructor
  · nlinarith [Nat.mul_le_mul_left L cnot]
  · nlinarith [Nat.mul_le_mul_left L single]

/-- Separate CNOT and single-qubit ceilings of the exact complex execution pool. -/
lemma complexBudget_coordinate_bounds (m n L : Nat) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
        (.gate .cnot) (complexBudget m n L) ≤ (192 * m + 6) * L + 6 ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
        (.gate .singleQubit) (complexBudget m n L) ≤ (296 * m + 6) * L + 13 := by
  cases L with
  | zero => simp [complexBudget, reduceCtorEq]
  | succ L =>
      obtain ⟨cnot, single⟩ :=
        complexPhase_coordinate_bounds (UnitarySource.model (m + n) true true false) m n
      simp only [complexBudget, Nat.succ_ne_zero, if_false, expanded_native_count,
        replacementCount, reduceCtorEq]
      unfold KnownZero.Total.Four.complexBudget KnownZero.Total.Four.unmatchedBudget
      simp only [Nat.succ_sub_one]
      split_ifs <;>
        simp [reduceCtorEq, KnownZero.Total.Four.budget, KnownZero.Total.Four.eventPool,
          KnownZero.Total.Four.phaseBudget] <;>
        constructor <;>
        nlinarith [Nat.mul_le_mul_left (L + 1) cnot, Nat.mul_le_mul_left (L + 1) single]

end

end QuantumAlg.QSP.MultiQubit.QSVT.Execution
