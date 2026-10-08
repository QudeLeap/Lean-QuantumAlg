/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Events
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Depth

/-!
# Scalar serial depth of the complete native finite retry

The complete measured round pays its compiled member, terminal measurements,
packing, physical bank measurement and correction, and literal seed reload.
The classical formula includes shared initialization, all 120 reusable pairs,
every original candidate offset, and the final factor selection. No runtime
context, circuit tree, or finite list of candidate instructions is evaluated.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent complete-round ceiling in the three actual register widths. -/
def roundDepthWidthBound (m ell width : Nat) : Nat :=
  compiledCircuitEventUnitDepthWidthBound m ell width + (m + 2 * ell) + 1 +
    3 * (m + 2 * ell + 2 * width)

/-- Independent full classical recovery ceiling, including 120 pairs and 404,685 slots per pair. -/
def recoveryDepthWidthBound (modulusWidth m ell coordinateWidth : Nat) : Nat :=
  12 * modulusWidth + 19 + 120 *
    (13 + (8 * m + 12 * ell + 258 + 264 * (12 * (ell + m) + 10)) +
      (m + 3) + (12 * modulusWidth + 8) +
      (1 + (85 * 69 ^ 2) * (170 + 2 * modulusWidth + 6 * coordinateWidth)) +
      (14 * (coordinateWidth + 1) + 38))

/-- The scalar ceiling includes initial preparation and loading within the round-width slack. -/
def scalarDepthBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 164 +
        16 * roundDepthWidthBound (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
        recoveryDepthWidthBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 2

/-- The existing full-round envelope is bounded without inspecting any compiled member. -/
theorem round_unitDepthBound_le_widthBound (m ell width N : Nat) :
    RuntimeRound.unitDepthBound m ell width N ≤ roundDepthWidthBound m ell width := by
  have member := compiledCircuitEventUnitDepth_le_widthBound m ell width N
  have reload := shortDLP_reload_count_le m ell width N
  rw [totalQubits_eq] at reload
  unfold RuntimeRound.unitDepthBound roundDepthWidthBound
  rw [totalQubits_eq]
  change _ + ((ell + m + ell) + (1 + (2 * (m + 2 * ell + 2 * width) + _))) ≤ _
  omega

private theorem offset_magnitude_le (offset : NumberTheory.IntegerPoint3)
    (member : offset ∈ LatticeCandidateScan.offsets.toList) :
    offset.1.natAbs + offset.2.1.natAbs + offset.2.2.natAbs ≤ 110 := by
  rw [LatticeCandidateScan.offsets, NumberTheory.toList_coefficientOffsetVector3,
    NumberTheory.mem_coefficientOffsetList3, NumberTheory.mem_coefficientOffsetBox3] at member
  change -(42 : Int) ≤ offset.1 ∧ offset.1 ≤ 42 ∧
    -(34 : Int) ≤ offset.2.1 ∧ offset.2.1 ≤ 34 ∧
      -(34 : Int) ≤ offset.2.2 ∧ offset.2.2 ≤ 34 at member
  have abs_le (value : Int) (bound : Nat)
      (lower : -(bound : Int) ≤ value) (upper : value ≤ (bound : Int)) :
      value.natAbs ≤ bound := by
    cases value <;> omega
  have first := abs_le offset.1 42 member.1 member.2.1
  have second := abs_le offset.2.1 34 member.2.2.1 member.2.2.2.1
  have third := abs_le offset.2.2 34 member.2.2.2.2.1 member.2.2.2.2.2
  omega

private theorem offsets_depth_le (coordinateWidth modulusWidth : Nat)
    (items : List NumberTheory.IntegerPoint3)
    (bounded : ∀ offset ∈ items,
      offset.1.natAbs + offset.2.1.natAbs + offset.2.2.natAbs ≤ 110) :
    LatticeCandidateScan.offsetsDepthBound coordinateWidth modulusWidth items ≤
      items.length * (170 + 2 * modulusWidth + 6 * coordinateWidth) := by
  induction items with
  | nil =>
    simp only [LatticeCandidateScan.offsetsDepthBound, List.length_nil, Nat.zero_mul, le_refl]
  | cons offset tail inductionHypothesis =>
    have magnitude := bounded offset List.mem_cons_self
    have first : LatticeCandidateSlotMachine.candidateSlotDepthBound
        coordinateWidth modulusWidth offset ≤ 170 + 2 * modulusWidth + 6 * coordinateWidth := by
      unfold LatticeCandidateSlotMachine.candidateSlotDepthBound
        LatticeOffsetMaterializer.operationCount
      omega
    have later := inductionHypothesis (fun item member =>
      bounded item (List.mem_cons_of_mem offset member))
    have combined := Nat.add_le_add first later
    simpa only [LatticeCandidateScan.offsetsDepthBound, List.length_cons,
      Nat.succ_mul, Nat.add_comm] using combined

private theorem scan_depth_le (coordinateWidth modulusWidth : Nat) :
    LatticeCandidateScan.scanDepthBound coordinateWidth modulusWidth ≤
      (85 * 69 ^ 2) * (170 + 2 * modulusWidth + 6 * coordinateWidth) := by
  have bounded := offsets_depth_le coordinateWidth modulusWidth
    LatticeCandidateScan.offsets.toList offset_magnitude_le
  have count : LatticeCandidateScan.offsets.toList.length = 85 * 69 ^ 2 := by
    rw [List.Vector.toList_length]
    exact NumberTheory.nearestPlaneCoefficientBounds3_work
  simpa only [LatticeCandidateScan.scanDepthBound, count] using bounded

private theorem nearest_depth_le (N : Nat) :
    LatticePairNearestPlaneSavedTarget.operationBound N ≤
      8 * shortLogBits N + 12 * tradeoffBits N + 258 +
        264 * (12 * (tradeoffBits N + shortLogBits N) + 10) := by
  have measured : measurementBits N = shortLogBits N + 2 * tradeoffBits N := by
    unfold measurementBits
    omega
  unfold LatticePairNearestPlaneSavedTarget.operationBound LatticeWideLllMachine.operationBound
    LatticeWideLllMachine.decodeTargetOperationBound LatticeWideInitializationPrefix.operationBound
  rw [measured]
  change 2 * (2 * (shortLogBits N + 2 * tradeoffBits N) + tradeoffBits N + 3) +
    (2 * (tradeoffBits N + shortLogBits N) + 8) + (2 * shortLogBits N + 16) +
      (32 + 130 * (12 * (tradeoffBits N + shortLogBits N) + 10)) + 131 ≤ _
  omega

/-- The original classical dependency allowance obeys the closed formula over scalar widths. -/
theorem recovery_depthBound_le_widthBound (N : Nat) :
    LatticeFixedBatchRecoveryMachine.depthBound N ≤
      recoveryDepthWidthBound (modulusBits N) (shortLogBits N) (tradeoffBits N)
        (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) := by
  have nearest := nearest_depth_le N
  have scan := scan_depth_le
    (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) (modulusBits N)
  have count : LatticePairRecoveryFold.PairCount = 120 := by
    norm_num [LatticePairRecoveryFold.PairCount, Nat.choose]
  unfold LatticeFixedBatchRecoveryMachine.depthBound LatticeBatchRecoveryWorkspaceBody.depthBound
    LatticeSharedQuadraticInitialization.depthBound LatticeBatchRecoveryEndpoint.depthBound
    LatticeBatchRecoveryTail.depthBound LatticePairRecoveryFold.depthBound
    LatticePairReusableRecovery.depthBound LatticePairFactorRecovery.depthBound
    LatticePairCandidateRecovery.recoveryDepthBound LatticePairCandidateRecovery.prefixDepthBound
    LatticePairCandidateRecovery.sharedDepthBound
    LatticeCandidateScanInitialized.initializedScanDepthBound recoveryDepthWidthBound
  rw [count]
  unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width
  change 12 * modulusBits N + 12 +
    (5 + 120 * (13 +
      (LatticePairNearestPlaneSavedTarget.operationBound N +
        (shortLogBits N + 3 + (12 * modulusBits N + 8)) + (1 + _) +
        (7 * ((_ + 1) + (_ + 1)) + 38))) + 2) ≤ _
  omega

/-- Every requested count's original allowance is bounded by the independent scalar formula. -/
theorem depthBound_le_scalarDepthBound (N totalRounds : Nat) :
    depthBound N totalRounds ≤ scalarDepthBound N totalRounds := by
  cases totalRounds with
  | zero => exact Nat.le_refl 0
  | succ count =>
    have member := compiledCircuitEventUnitDepth_le_widthBound
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    have reload := seedReload_count_le_one
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    have bank := bank_qubits_ge_three N
    have nonempty : ShortDLP.totalQubits
        (ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) ≠ 0 := by
      omega
    have round :
        RuntimeRound.unitDepthBound (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N + 1 ≤
          roundDepthWidthBound (shortLogBits N) (tradeoffBits N) (arithmeticBits N) := by
      rw [totalQubits_eq] at bank
      unfold RuntimeRound.unitDepthBound roundDepthWidthBound
      rw [totalQubits_eq]
      change _ + ((tradeoffBits N + shortLogBits N + tradeoffBits N) +
        (1 + (2 * (shortLogBits N + 2 * tradeoffBits N + 2 * arithmeticBits N) + _))) + 1 ≤ _
      omega
    have recovery := recovery_depthBound_le_widthBound N
    have batch := Nat.add_le_add (Nat.mul_le_mul_left 16 round) recovery
    have repeated := Nat.mul_le_mul_left (count + 1) batch
    unfold depthBound NativeRetrySelection.depthBound NativeRetryChain.depthBound
      NativeRetryChain.suffixDepthBound NativeBatchRecovery.depthBound
      NativeBatchReuseRecovery.depthBound NativeBatch.unitDepthBound NativeBatchReuse.unitDepthBound
      scalarDepthBound
    rw [if_neg nonempty]
    nlinarith

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The complete actual code path satisfies the same closed scalar serial ceiling. -/
theorem code_depth_le_scalar (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).depth (fun _ => 1) path ≤
      scalarDepthBound N totalRounds :=
  (code_depth_le base noQuantum input totalRounds path).trans
    (depthBound_le_scalarDepthBound N totalRounds)

/-- The complete actual run path, including all classical work, satisfies the scalar ceiling. -/
theorem run_depth_le_scalar (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.depth (fun _ => 1) path ≤
      scalarDepthBound N totalRounds :=
  (run_depth_le base noQuantum input totalRounds path).trans
    (depthBound_le_scalarDepthBound N totalRounds)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
