/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Counts
import Mathlib.Tactic.NormNum

/-!
# Kernel-checked fixed-width native allowances

The small balanced-recursion evaluations are shared rather than expanding a
large recursive expression independently in each endpoint.
-/

namespace QuantumAlg.MAU.Addition.HRS

private lemma oneDirtyXBound_value_1 : oneDirtyXBound 1 = 1 := by
  rw [oneDirtyXBound]
  norm_num
private lemma oneDirtyCnotBound_value_1 : oneDirtyCnotBound 1 = 0 := by
  rw [oneDirtyCnotBound]
  norm_num
private lemma oneDirtyToffoliBound_value_1 : oneDirtyToffoliBound 1 = 0 := by
  rw [oneDirtyToffoliBound]
  norm_num
private lemma oneDirtyXBound_value_2 : oneDirtyXBound 2 = 2 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_1]
private lemma oneDirtyCnotBound_value_2 : oneDirtyCnotBound 2 = 8 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_1]
private lemma oneDirtyToffoliBound_value_2 : oneDirtyToffoliBound 2 = 4 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_1]
private lemma oneDirtyXBound_value_3 : oneDirtyXBound 3 = 7 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_2, oneDirtyXBound_value_1]
private lemma oneDirtyCnotBound_value_3 : oneDirtyCnotBound 3 = 16 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_2,
    oneDirtyCnotBound_value_1]
private lemma oneDirtyToffoliBound_value_3 : oneDirtyToffoliBound 3 = 10 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_2,
    oneDirtyToffoliBound_value_1]
private lemma oneDirtyXBound_value_4 : oneDirtyXBound 4 = 8 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_2]
private lemma oneDirtyCnotBound_value_4 : oneDirtyCnotBound 4 = 30 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_2]
private lemma oneDirtyToffoliBound_value_4 : oneDirtyToffoliBound 4 = 58 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_2]
private lemma oneDirtyXBound_value_5 : oneDirtyXBound 5 = 21 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_3, oneDirtyXBound_value_2]
private lemma oneDirtyCnotBound_value_5 : oneDirtyCnotBound 5 = 42 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_3,
    oneDirtyCnotBound_value_2]
private lemma oneDirtyToffoliBound_value_5 : oneDirtyToffoliBound 5 = 70 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_3,
    oneDirtyToffoliBound_value_2]
private lemma oneDirtyXBound_value_8 : oneDirtyXBound 8 = 36 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_4]
private lemma oneDirtyCnotBound_value_8 : oneDirtyCnotBound 8 = 94 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_4]
private lemma oneDirtyToffoliBound_value_8 : oneDirtyToffoliBound 8 = 284 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_4]
private lemma oneDirtyXBound_value_9 : oneDirtyXBound 9 = 57 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_5, oneDirtyXBound_value_4]
private lemma oneDirtyCnotBound_value_9 : oneDirtyCnotBound 9 = 110 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_5,
    oneDirtyCnotBound_value_4]
private lemma oneDirtyToffoliBound_value_9 : oneDirtyToffoliBound 9 = 304 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_5,
    oneDirtyToffoliBound_value_4]
private lemma oneDirtyXBound_value_16 : oneDirtyXBound 16 = 124 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_8]
private lemma oneDirtyCnotBound_value_16 : oneDirtyCnotBound 16 = 262 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_8]
private lemma oneDirtyToffoliBound_value_16 : oneDirtyToffoliBound 16 = 976 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_8]
private lemma oneDirtyXBound_value_17 : oneDirtyXBound 17 = 153 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_9, oneDirtyXBound_value_8]
private lemma oneDirtyCnotBound_value_17 : oneDirtyCnotBound 17 = 282 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_9,
    oneDirtyCnotBound_value_8]
private lemma oneDirtyToffoliBound_value_17 : oneDirtyToffoliBound 17 = 1004 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_9,
    oneDirtyToffoliBound_value_8]
private lemma oneDirtyXBound_value_32 : oneDirtyXBound 32 = 364 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_16]
private lemma oneDirtyCnotBound_value_32 : oneDirtyCnotBound 32 = 678 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_16]
private lemma oneDirtyToffoliBound_value_32 : oneDirtyToffoliBound 32 = 2840 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_16]
private lemma oneDirtyXBound_value_33 : oneDirtyXBound 33 = 401 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_17, oneDirtyXBound_value_16]
private lemma oneDirtyCnotBound_value_33 : oneDirtyCnotBound 33 = 702 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_17,
    oneDirtyCnotBound_value_16]
private lemma oneDirtyToffoliBound_value_33 : oneDirtyToffoliBound 33 = 2876 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_17,
    oneDirtyToffoliBound_value_16]
private lemma oneDirtyXBound_value_64 : oneDirtyXBound 64 = 972 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_32]
private lemma oneDirtyCnotBound_value_64 : oneDirtyCnotBound 64 = 1670 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_32]
private lemma oneDirtyToffoliBound_value_64 : oneDirtyToffoliBound 64 = 7528 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_32]
private lemma oneDirtyXBound_value_65 : oneDirtyXBound 65 = 1017 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_33, oneDirtyXBound_value_32]
private lemma oneDirtyCnotBound_value_65 : oneDirtyCnotBound 65 = 1698 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_33,
    oneDirtyCnotBound_value_32]
private lemma oneDirtyToffoliBound_value_65 : oneDirtyToffoliBound 65 = 7572 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_33,
    oneDirtyToffoliBound_value_32]
private lemma oneDirtyXBound_value_128 : oneDirtyXBound 128 = 2444 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_64]
private lemma oneDirtyCnotBound_value_128 : oneDirtyCnotBound 128 = 3974 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_64]
private lemma oneDirtyToffoliBound_value_128 : oneDirtyToffoliBound 128 = 18824 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_64]
private lemma oneDirtyXBound_value_129 : oneDirtyXBound 129 = 2497 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_65, oneDirtyXBound_value_64]
private lemma oneDirtyCnotBound_value_129 : oneDirtyCnotBound 129 = 4006 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_65,
    oneDirtyCnotBound_value_64]
private lemma oneDirtyToffoliBound_value_129 : oneDirtyToffoliBound 129 = 18876 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_65,
    oneDirtyToffoliBound_value_64]
private lemma oneDirtyXBound_value_256 : oneDirtyXBound 256 = 5900 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_128]
private lemma oneDirtyCnotBound_value_256 : oneDirtyCnotBound 256 = 9222 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_128]
private lemma oneDirtyToffoliBound_value_256 : oneDirtyToffoliBound 256 = 45256 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_128]
private lemma oneDirtyXBound_value_257 : oneDirtyXBound 257 = 5961 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_129, oneDirtyXBound_value_128]
private lemma oneDirtyCnotBound_value_257 : oneDirtyCnotBound 257 = 9258 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_129,
    oneDirtyCnotBound_value_128]
private lemma oneDirtyToffoliBound_value_257 : oneDirtyToffoliBound 257 = 45316 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_129,
    oneDirtyToffoliBound_value_128]
private lemma oneDirtyXBound_value_512 : oneDirtyXBound 512 = 13836 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_256]
private lemma oneDirtyCnotBound_value_512 : oneDirtyCnotBound 512 = 20998 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_256]
private lemma oneDirtyToffoliBound_value_512 : oneDirtyToffoliBound 512 = 105800 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_256]
private lemma oneDirtyXBound_value_513 : oneDirtyXBound 513 = 13905 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_257, oneDirtyXBound_value_256]
private lemma oneDirtyCnotBound_value_513 : oneDirtyCnotBound 513 = 21038 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_257,
    oneDirtyCnotBound_value_256]
private lemma oneDirtyToffoliBound_value_513 : oneDirtyToffoliBound 513 = 105868 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_257,
    oneDirtyToffoliBound_value_256]
private lemma oneDirtyXBound_value_1024 : oneDirtyXBound 1024 = 31756 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_512]
private lemma oneDirtyCnotBound_value_1024 : oneDirtyCnotBound 1024 = 47110 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_512]
private lemma oneDirtyToffoliBound_value_1024 : oneDirtyToffoliBound 1024 = 242248 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_512]
private lemma oneDirtyXBound_value_1025 : oneDirtyXBound 1025 = 31833 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_513, oneDirtyXBound_value_512]
private lemma oneDirtyCnotBound_value_1025 : oneDirtyCnotBound 1025 = 47154 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_513,
    oneDirtyCnotBound_value_512]
private lemma oneDirtyToffoliBound_value_1025 : oneDirtyToffoliBound 1025 = 242324 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_513,
    oneDirtyToffoliBound_value_512]
private lemma oneDirtyXBound_value_2048 : oneDirtyXBound 2048 = 71692 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_1024]
private lemma oneDirtyCnotBound_value_2048 : oneDirtyCnotBound 2048 = 104454 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_1024]
private lemma oneDirtyToffoliBound_value_2048 : oneDirtyToffoliBound 2048 = 545864 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_1024]
private lemma oneDirtyXBound_value_2049 : oneDirtyXBound 2049 = 71777 := by
  rw [oneDirtyXBound]
  norm_num [lowWidth, highWidth, carryXBound, oneDirtyXBound_value_1025, oneDirtyXBound_value_1024]
private lemma oneDirtyCnotBound_value_2049 : oneDirtyCnotBound 2049 = 104502 := by
  rw [oneDirtyCnotBound]
  norm_num [lowWidth, highWidth, carryCnotBound, oneDirtyCnotBound_value_1025,
    oneDirtyCnotBound_value_1024]
private lemma oneDirtyToffoliBound_value_2049 : oneDirtyToffoliBound 2049 = 545948 := by
  rw [oneDirtyToffoliBound]
  norm_num [lowWidth, highWidth, carryToffoliBound, oneDirtyToffoliBound_value_1025,
    oneDirtyToffoliBound_value_1024]

/-- Kernel-checked coordinate values for a 2048-bit word. -/
lemma hrsOneDirty_bounds_2048 :
    oneDirtyXBound 2048 = 71692 ∧ oneDirtyCnotBound 2048 = 104454 ∧
      oneDirtyToffoliBound 2048 = 545864 :=
  ⟨oneDirtyXBound_value_2048, oneDirtyCnotBound_value_2048, oneDirtyToffoliBound_value_2048⟩

/-- The comparison's extended word uses the same recurrences at width 2049. -/
lemma hrsOneDirty_bounds_2049 :
    oneDirtyXBound 2049 = 71777 ∧ oneDirtyCnotBound 2049 = 104502 ∧
      oneDirtyToffoliBound 2049 = 545948 :=
  ⟨oneDirtyXBound_value_2049, oneDirtyCnotBound_value_2049, oneDirtyToffoliBound_value_2049⟩

end QuantumAlg.MAU.Addition.HRS
