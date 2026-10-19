/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Resources
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Counts

/-!
# Actual native counts including internal work initialization

The identity residue is either zero or one, so loading and unloading it
requires at most two X gates in total. Preparing the two work words is charged
separately. Both actual selected-power CNOT ledgers surround the literal
arbitrary-target XOR copy. The selected arithmetic still emits no X gates.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open EncodedBit.GateSpec

private lemma constantOneIndices_length_le_one {width : Nat} (value : Fin (2 ^ width))
    (small : value.val ≤ 1) : (EncodedBit.Word.constantOneIndices value).length ≤ 1 := by
  cases width with
  | zero =>
      exact (EncodedBit.Word.constantOneIndices_length_le value).trans (by omega)
  | succ width =>
      apply (EncodedBit.Word.constantOneIndices_nodup value).length_le_of_subset
        (l₂ := [⟨0, Nat.zero_lt_succ width⟩])
      intro bit present
      have selected := (EncodedBit.Word.mem_constantOneIndices value bit).mp present
      have one : value.val = 1 := by
        have nonzero : value.val ≠ 0 := by
          intro zero
          simp [zero] at selected
        omega
      rw [one, Nat.testBit_one_eq_true_iff_self_eq_zero] at selected
      simp only [List.mem_singleton]
      exact Fin.ext selected

private lemma identityLoadGates_x_count_le_one (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    ((identityLoadGates exponentWidth width modulus positive).map xMultiplicity).sum ≤ 1 := by
  rw [identityLoadGates, EncodedBit.Word.xorConstantGates_xMultiplicity_sum]
  apply constantOneIndices_length_le_one
  rw [Nat.FixedWidth.unitResidueWord_one_val]
  exact Nat.mod_le 1 modulus.val

private lemma nativeSource_cnot_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost =
        2 * selectedPowerCount exponentWidth width modulus base .cnot + width := by
  have load : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (identityLoadProgram exponentWidth width modulus positive).eventCost = 0 :=
    (programList_cnot_count_eq_sum (nativeQubitLayout exponentWidth width) .empty
      (identityLoadGates exponentWidth width modulus positive)).trans
        (EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum _ _)
  have unload : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (identityUnloadProgram exponentWidth width modulus positive).eventCost = 0 := by
    refine (programList_cnot_count_eq_sum (nativeQubitLayout exponentWidth width) .empty
      (identityLoadGates exponentWidth width modulus positive).reverse).trans ?_
    rw [List.map_reverse, List.sum_reverse, identityLoadGates,
      EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum]
  rw [arithmeticNativeSourceProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ResourcePool.count_add,
    placedArithmeticOracle_eventCost, gidneyExponentOracle_cnot_count, load, unload]
  omega

private lemma nativeSource_singleQubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost ≤
        2 := by
  have load : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (identityLoadProgram exponentWidth width modulus positive).eventCost ≤ 1 :=
    (programList_x_count_eq_sum (nativeQubitLayout exponentWidth width) .empty
      (identityLoadGates exponentWidth width modulus positive)).trans_le
        (identityLoadGates_x_count_le_one exponentWidth width modulus positive)
  have unload : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (identityUnloadProgram exponentWidth width modulus positive).eventCost ≤ 1 := by
    refine (programList_x_count_eq_sum (nativeQubitLayout exponentWidth width) .empty
      (identityLoadGates exponentWidth width modulus positive).reverse).trans_le ?_
    simpa only [List.map_reverse, List.sum_reverse] using
      identityLoadGates_x_count_le_one exponentWidth width modulus positive
  rw [arithmeticNativeSourceProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, ResourcePool.count_add, ResourcePool.count_add,
    placedArithmeticOracle_eventCost, gidneyExponentOracle_singleQubit_count]
  omega

private lemma preparedCode_gate_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (coordinate : AlgorithmGate.Coordinate)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        ((arithmeticNativeCode exponentWidth width modulus positive base).resourcePool path) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate coordinate)
        (arithmeticNativeSourceProgram exponentWidth width modulus positive base).eventCost := by
  change ResourcePool.count _ (ResourcePool.ofList
    (ZeroPreparation.eventTrace AlgorithmGate.model .empty (workLayout exponentWidth width) ++
      (arithmeticNativeUnitary exponentWidth width modulus positive base).eventTrace)) = _
  rw [ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    arithmeticNativeUnitary_eventCost, ResourcePool.count_add]
  change ResourcePool.count _ (ZeroPreparation.eventCost AlgorithmGate.model .empty
    (workLayout exponentWidth width)) + _ = _
  rw [ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model .empty
    (workLayout exponentWidth width) 2 (fun _ => rfl)]
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton,
    reduceCtorEq, ↓reduceIte, Nat.mul_zero, Nat.zero_add]

/-- Both arithmetic CNOT ledgers and the literal target copy belong to this execution. -/
lemma arithmeticNativeCode_cnot_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      ((arithmeticNativeCode exponentWidth width modulus positive base).resourcePool path) =
        2 * selectedPowerCount exponentWidth width modulus base .cnot + width := by
  rw [preparedCode_gate_count, nativeSource_cnot_count]

/-- The actual prepared CNOT count obeys the independent selected-power allowance. -/
lemma arithmeticNativeCode_cnot_count_le (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      ((arithmeticNativeCode exponentWidth width modulus positive base).resourcePool path) ≤
        2 * selectedPowerCnotBound exponentWidth width + width := by
  rw [arithmeticNativeCode_cnot_count]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (selectedPowerCount_cnot_le exponentWidth width modulus base)) width

/-- At most two single-qubit gates load and unload the actual identity residue. -/
lemma arithmeticNativeCode_singleQubit_count (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (path : (arithmeticNativeCode exponentWidth width modulus positive base).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      ((arithmeticNativeCode exponentWidth width modulus positive base).resourcePool path) ≤
        2 := by
  rw [preparedCode_gate_count]
  exact nativeSource_singleQubit_count exponentWidth width modulus positive base

end

end QuantumAlg.MAU.Exponentiation.Gidney
