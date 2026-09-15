/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.ClassicalCoordinates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Specification

/-!
# Exact quantum coordinates of the actual original-bank retry

The actual source, recovery and selector have zero nonclassical coordinates.
Every original member therefore contributes its exact query and QFT labels,
while paid resets retain their distinct correction labels. The statements
observe the existing finite run and its real paths, including zero batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite

open Execution

noncomputable section

private theorem count_zero_of_le {kind : ProblemKind} (event : Resource.Event kind)
    {actual allowance : ResourcePool kind} (bounded : actual ≤ allowance)
    (zero : ResourcePool.count event allowance = 0) : ResourcePool.count event actual = 0 :=
  Nat.eq_zero_of_le_zero (zero ▸ ResourcePool.le_iff_count.mp bounded event)

private theorem range_count {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (event : Resource.Event kind) (count : Nat) (body : Fin count → Circuit ctx ctx)
    (amount : Nat) (equations : ∀ index path, ResourcePool.count event
      ((body index).resourcePool path) = amount) (path : (Circuit.forRange count body).Path) :
    ResourcePool.count event ((Circuit.forRange count body).resourcePool path) =
      count * amount := by
  induction count with
  | zero =>
      change ResourcePool.count event (0 : ResourcePool kind) = 0 * amount
      simp
  | succ count ih =>
      change ResourcePool.count event
        ((body 0).resourcePool path.1 +
          (Circuit.forRange count (fun index => body index.succ)).resourcePool path.2) = _
      erw [ResourcePool.count_add, equations, ih _ (fun index => equations index.succ)]
      ring

section ExactMemberMultiplicity

variable (event : Resource.Event .quantum)
    (outside : ∀ label, event ≠ .classicalOperation label)
    (N : Nat) (preparedZero : ResourcePool.count event
      (ResourcePool.singleton (preparation N).event) = 0)
    (resetZero : ResourcePool.count event
      (ZReset.Bank.envelope (ShortDLP.totalQubits (parameters N))) = 0)

include outside

private theorem selection_zero : ResourcePool.count event (Retry.selectionEventBudget N) = 0 := by
  simp [Retry.selectionEventBudget, ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace, outside, eq_comm]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

omit outside in
include resetZero in
private theorem reset_zero (path : (resetBank base noQuantum N).Path) :
    ResourcePool.count event ((resetBank base noQuantum N).resourcePool path) = 0 := by
  have bound := ZReset.BankScope.zResetBankScope_resourcePool_le
    (nativeOracle_context_qubits N (nativeOracle_context_wires base noQuantum N)) path
  erw [context_width base noQuantum N] at bound
  exact count_zero_of_le event bound resetZero

include preparedZero in
private theorem setup_zero (path : (Batch.setup base noQuantum N).Path) :
    ResourcePool.count event ((Batch.setup base noQuantum N).resourcePool path) = 0 := by
  apply count_zero_of_le event (Batch.setup_pool base noQuantum N path)
  simp only [Batch.setupEventBudget, Batch.sourceEventBudget, ResourcePool.count_add,
    nativeOracle_source_count_eq_zero event outside, preparedZero, add_zero]

private theorem redraw_zero (path : (Batch.redraw base noQuantum N).Path) :
    ResourcePool.count event ((Batch.redraw base noQuantum N).resourcePool path) = 0 := by
  exact count_zero_of_le event (Batch.redraw_pool base noQuantum N path)
    (nativeOracle_source_count_eq_zero event outside N)

private theorem copy_zero (index : Fin 16) (path : (Batch.copy base noQuantum N index).Path) :
    ResourcePool.count event ((Batch.copy base noQuantum N index).resourcePool path) = 0 := by
  erw [Batch.copy_pool]
  simp [Batch.copyEvent, outside, eq_comm]

include resetZero in
private theorem reused_count (input : Input N) (index : Fin 16)
    (path : (Batch.reusedSample base noQuantum N input index).Path) :
    ResourcePool.count event
      ((Batch.reusedSample base noQuantum N input index).resourcePool path) =
        ResourcePool.count event (memberEventBudget N) := by
  change ResourcePool.count event
    (((resetBank (Batch.storageContext base N) (Batch.storage_empty base noQuantum N)
      N).resourcePool path.1.1 + (body (Batch.storageContext base N)
        (Batch.storage_empty base noQuantum N) N input
        (Batch.parameter base N)).resourcePool path.1.2) +
      (Batch.copy base noQuantum N index).resourcePool path.2) = _
  erw [ResourcePool.count_add, ResourcePool.count_add,
    reset_zero event N resetZero (Batch.storageContext base N)
      (Batch.storage_empty base noQuantum N),
    body_pool, copy_zero event outside N base noQuantum, zero_add, add_zero]

include resetZero in
private theorem first_batch_count (input : Input N)
    (path : (Batch.firstBatch base noQuantum N input).Path) :
    ResourcePool.count event ((Batch.firstBatch base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  have tail := range_count event 15
    (fun index => Batch.reusedSample base noQuantum N input index.succ)
    (ResourcePool.count event (memberEventBudget N))
    (fun index => reused_count event outside N resetZero base noQuantum input index.succ) path.2
  have head := congrArg (ResourcePool.count event)
    (body_pool (Batch.storageContext base N) (Batch.storage_empty base noQuantum N) N
      input (Batch.parameter base N) path.1.1)
  have copied := copy_zero event outside N base noQuantum 0 path.1.2
  change ResourcePool.count event
    (((body (Batch.storageContext base N) (Batch.storage_empty base noQuantum N) N input
      (Batch.parameter base N)).resourcePool path.1.1 +
        (Batch.copy base noQuantum N 0).resourcePool path.1.2) +
      (Circuit.forRange 15
        (fun index => Batch.reusedSample base noQuantum N input index.succ)).resourcePool
          path.2) = _
  erw [ResourcePool.count_add, ResourcePool.count_add]
  omega

include preparedZero resetZero in
private theorem batch_count (input : Input N) (path : (Batch.code base noQuantum N input).Path) :
    ResourcePool.count event ((Batch.code base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  change ResourcePool.count event
    ((Batch.setup base noQuantum N).resourcePool path.1 +
      (Batch.firstBatch base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, setup_zero event outside N preparedZero base noQuantum,
    first_batch_count event outside N resetZero base noQuantum, zero_add]

include resetZero in
private theorem next_batch_count (input : Input N)
    (path : (Batch.nextBatch base noQuantum N input).Path) :
    ResourcePool.count event ((Batch.nextBatch base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  have tail := range_count event 16 (Batch.reusedSample base noQuantum N input)
    (ResourcePool.count event (memberEventBudget N))
    (reused_count event outside N resetZero base noQuantum input) path.2
  change ResourcePool.count event
    ((Batch.redraw base noQuantum N).resourcePool path.1 +
      (Circuit.forRange 16 (Batch.reusedSample base noQuantum N input)).resourcePool path.2) = _
  erw [ResourcePool.count_add, redraw_zero event outside N base noQuantum, tail, zero_add]

private theorem recovery_zero (input : Input N)
    (path : (Batch.Recovery.into base noQuantum N input).Path) :
    ResourcePool.count event ((Batch.Recovery.into base noQuantum N input).resourcePool path) =
      0 :=
  count_zero_of_le event (Batch.Recovery.recovery_pool base noQuantum N input path)
    (nativeOracle_recovery_count_eq_zero event outside N)

include preparedZero resetZero in
private theorem recovery_first_count (input : Input N)
    (path : (Batch.Recovery.first base noQuantum N input).Path) :
    ResourcePool.count event ((Batch.Recovery.first base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  change ResourcePool.count event
    ((Batch.code base noQuantum N input).resourcePool path.1 +
      (Batch.Recovery.into base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, batch_count event outside N preparedZero resetZero base noQuantum,
    recovery_zero event outside N base noQuantum, add_zero]

include resetZero in
private theorem recovery_next_count (input : Input N)
    (path : (Batch.Recovery.next base noQuantum N input).Path) :
    ResourcePool.count event ((Batch.Recovery.next base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  change ResourcePool.count event
    ((Batch.nextBatch base noQuantum N input).resourcePool path.1 +
      (Batch.Recovery.into base noQuantum N input).resourcePool path.2) = _
  erw [ResourcePool.count_add, next_batch_count event outside N resetZero base noQuantum,
    recovery_zero event outside N base noQuantum, add_zero]

private theorem select_zero (path : (Retry.select base noQuantum N).Path) :
    ResourcePool.count event ((Retry.select base noQuantum N).resourcePool path) = 0 :=
  count_zero_of_le event (Retry.selection_pool base noQuantum N path)
    (selection_zero event outside N)

include preparedZero resetZero in
private theorem first_count (input : Input N) (path : (Retry.first base noQuantum N input).Path) :
    ResourcePool.count event ((Retry.first base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  change ResourcePool.count event (0 +
    ((Batch.Recovery.first (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N
      input).resourcePool path.2.1 + (Retry.select base noQuantum N).resourcePool path.2.2)) = _
  erw [zero_add, ResourcePool.count_add,
    recovery_first_count event outside N preparedZero resetZero (Retry.callerContext base N)
      (Retry.caller_empty base noQuantum N), select_zero event outside N base noQuantum, add_zero]

include resetZero in
private theorem next_count (input : Input N) (path : (Retry.next base noQuantum N input).Path) :
    ResourcePool.count event ((Retry.next base noQuantum N input).resourcePool path) =
      16 * ResourcePool.count event (memberEventBudget N) := by
  change ResourcePool.count event
    ((Batch.Recovery.next (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N
      input).resourcePool path.1 + (Retry.select base noQuantum N).resourcePool path.2) = _
  erw [ResourcePool.count_add,
    recovery_next_count event outside N resetZero (Retry.callerContext base N)
      (Retry.caller_empty base noQuantum N), select_zero event outside N base noQuantum, add_zero]

include preparedZero resetZero in
private theorem positive_count (input : Input N) (laterCount : Nat)
    (path : (Retry.code base noQuantum N input laterCount).Path) :
    ResourcePool.count event ((Retry.code base noQuantum N input laterCount).resourcePool path) =
      (16 * (laterCount + 1)) * ResourcePool.count event (memberEventBudget N) := by
  have tail := range_count event laterCount (fun _ => Retry.next base noQuantum N input)
    (16 * ResourcePool.count event (memberEventBudget N))
    (fun _ => next_count event outside N resetZero base noQuantum input) path.2.1
  change ResourcePool.count event
    ((Retry.first base noQuantum N input).resourcePool path.1 +
      ((Circuit.forRange laterCount (fun _ => Retry.next base noQuantum N input)).resourcePool
        path.2.1 + ResourcePool.singleton (Retry.packEvent N))) = _
  simp only [ResourcePool.count_add, first_count event outside N preparedZero resetZero,
    tail, Retry.packEvent, ResourcePool.count_singleton, Ne.symm (outside _), if_false, add_zero]
  ring

include preparedZero resetZero in
private theorem finite_count (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.count event ((run base noQuantum N input count).code.resourcePool path) =
      (16 * count) * ResourcePool.count event (memberEventBudget N) := by
  cases count with
  | zero =>
      have empty := congrArg (ResourcePool.count event) (NativeRetryEmpty.code_pool base N path)
      change ResourcePool.count event ((NativeRetryEmpty.code base N).resourcePool path) =
        16 * 0 * ResourcePool.count event (memberEventBudget N)
      exact empty.trans (by simp)
  | succ count =>
      exact positive_count event outside N preparedZero resetZero base noQuantum input count path

end ExactMemberMultiplicity

private theorem member_query (N : Nat) :
    ResourcePool.count (ShortDLP.oracleEvent N (parameters N)) (memberEventBudget N) =
      1 := by
  simp +decide [memberEventBudget, ShortDLP.preparationCircuit_eventCost,
    ShortDLP.readoutCircuit_eventCost, QFTCircuit_eventCost_eq, WalshHadamard.hadamardEvent,
    ShortDLP.oracleEvent, qftControlledPhaseLabel, Circuit.zEvent]

private theorem member_hadamard (N : Nat) :
    ResourcePool.count (WalshHadamard.hadamardEvent) (memberEventBudget N) =
      2 * (ShortDLP.firstBits (parameters N) + (parameters N).ell) := by
  simp +decide [memberEventBudget, ShortDLP.preparationCircuit_eventCost,
    ShortDLP.readoutCircuit_eventCost, QFTCircuit_eventCost_eq, WalshHadamard.hadamardEvent,
    ShortDLP.oracleEvent, qftControlledPhaseLabel, Circuit.zEvent]
  omega

private theorem member_controlledPhase (N : Nat) :
    ResourcePool.count (qftControlledPhaseEvent) (memberEventBudget N) =
      (ShortDLP.firstBits (parameters N)).choose 2 + (parameters N).ell.choose 2 := by
  simp +decide [memberEventBudget, ShortDLP.preparationCircuit_eventCost,
    ShortDLP.readoutCircuit_eventCost, QFTCircuit_eventCost_eq, WalshHadamard.hadamardEvent,
    ShortDLP.oracleEvent, qftControlledPhaseEvent, qftControlledPhaseLabel, Circuit.zEvent]

private theorem member_swap (N : Nat) :
    ResourcePool.count (qftSwapEvent) (memberEventBudget N) =
      ShortDLP.firstBits (parameters N) / 2 + (parameters N).ell / 2 := by
  simp +decide [memberEventBudget, ShortDLP.preparationCircuit_eventCost,
    ShortDLP.readoutCircuit_eventCost, QFTCircuit_eventCost_eq, WalshHadamard.hadamardEvent,
    ShortDLP.oracleEvent, qftControlledPhaseLabel, qftSwapEvent,
    Gate.atomicEvent, Circuit.zEvent]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Exact actual query occurrences; reset corrections have distinct native labels. -/
theorem nativeOracle_finiteRetry_query_count (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.count (ShortDLP.oracleEvent N (parameters N))
      ((run base noQuantum N input count).code.resourcePool path) = 16 * count := by
  have equation := finite_count (ShortDLP.oracleEvent N (parameters N))
    (by intro label; simp [ShortDLP.oracleEvent]) N
    (by simp [BasisPreparation.event, ShortDLP.oracleEvent])
    (by simp +decide [ZReset.Bank.envelope, ZReset.eventEnvelope, List.ofFn_succ,
      ShortDLP.oracleEvent, ResourcePool.count])
    base noQuantum input count path
  rw [member_query] at equation
  exact equation.trans (by ring)

/-- Exact actual hadamard occurrences; reset corrections have distinct native labels. -/
theorem nativeOracle_finiteRetry_hadamard_count (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.count (WalshHadamard.hadamardEvent)
      ((run base noQuantum N input count).code.resourcePool path) = 32 * count *
        (ShortDLP.firstBits (parameters N) + (parameters N).ell) := by
  have equation := finite_count (WalshHadamard.hadamardEvent)
    (by intro label; simp [WalshHadamard.hadamardEvent]) N
    (by simp [BasisPreparation.event, WalshHadamard.hadamardEvent])
    (by simp +decide [ZReset.Bank.envelope, ZReset.eventEnvelope, List.ofFn_succ,
       WalshHadamard.hadamardEvent, ResourcePool.count])
    base noQuantum input count path
  rw [member_hadamard] at equation
  exact equation.trans (by ring)

/-- Exact actual controlledPhase occurrences; reset corrections have distinct native labels. -/
theorem nativeOracle_finiteRetry_controlledPhase_count (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.count (qftControlledPhaseEvent)
      ((run base noQuantum N input count).code.resourcePool path) = 16 * count *
        ((ShortDLP.firstBits (parameters N)).choose 2 + (parameters N).ell.choose 2) := by
  have equation := finite_count (qftControlledPhaseEvent)
    (by intro label; simp [qftControlledPhaseEvent]) N
    (by simp [BasisPreparation.event, qftControlledPhaseEvent])
    (by simp +decide [ZReset.Bank.envelope, ZReset.eventEnvelope, List.ofFn_succ,
        qftControlledPhaseEvent,
      qftControlledPhaseLabel, ResourcePool.count])
    base noQuantum input count path
  rw [member_controlledPhase] at equation
  exact equation.trans (by ring)

/-- Exact actual swap occurrences; reset corrections have distinct native labels. -/
theorem nativeOracle_finiteRetry_swap_count (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.count (qftSwapEvent)
      ((run base noQuantum N input count).code.resourcePool path) = 16 * count *
        (ShortDLP.firstBits (parameters N) / 2 + (parameters N).ell / 2) := by
  have equation := finite_count (qftSwapEvent)
    (by intro label; simp [qftSwapEvent, Gate.atomicEvent]) N
    (by simp [BasisPreparation.event, qftSwapEvent, Gate.atomicEvent])
    (by simp +decide [ZReset.Bank.envelope, ZReset.eventEnvelope, List.ofFn_succ,
       qftSwapEvent, Gate.atomicEvent, ResourcePool.count])
    base noQuantum input count path
  rw [member_swap] at equation
  exact equation.trans (by ring)

private theorem firstBits_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) : ShortDLP.firstBits (parameters pair.modulus) =
      n + 1 + (n + 2) / 2 := by
  simp only [ShortDLP.firstBits, parameters, shortLogBits_sameBit pair positive,
    tradeoffBits_sameBit pair positive, RSA.GeneratorOrder.m, RSA.GeneratorOrder.ell]
  omega

private theorem ell_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) :
    (parameters pair.modulus).ell = (n + 2) / 2 := by
  simp only [parameters, tradeoffBits_sameBit pair positive, RSA.GeneratorOrder.ell]

/-- The original same-bit Hadamard formula counts every actual preparation and inverse QFT. -/
theorem nativeOracle_finiteRetry_hadamard_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (input : Input pair.modulus) (count : Nat)
    (path : (run base noQuantum pair.modulus input count).code.Path) :
    ResourcePool.count WalshHadamard.hadamardEvent
      ((run base noQuantum pair.modulus input count).code.resourcePool path) =
        32 * count * (n + 1 + 2 * ((n + 2) / 2)) := by
  rw [nativeOracle_finiteRetry_hadamard_count, firstBits_sameBit pair positive,
    ell_sameBit pair positive]
  ring

private theorem phase_arithmetic (count first second : Nat) :
    16 * count * (first.choose 2 + second.choose 2) =
      8 * count * (first * (first - 1) + second * (second - 1)) := by
  have firstEq := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self first)
  have secondEq := Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self second)
  rw [Nat.choose_two_right, Nat.choose_two_right]
  have halfSum : 2 * (first * (first - 1) / 2 + second * (second - 1) / 2) =
      first * (first - 1) + second * (second - 1) := by omega
  calc
    _ = 8 * count * (2 * (first * (first - 1) / 2 + second * (second - 1) / 2)) := by ring
    _ = _ := congrArg (8 * count * ·) halfSum

/-- The same two inverse QFTs give the original exact controlled-phase formula. -/
theorem nativeOracle_finiteRetry_controlledPhase_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (input : Input pair.modulus) (count : Nat)
    (path : (run base noQuantum pair.modulus input count).code.Path) :
    ResourcePool.count qftControlledPhaseEvent
      ((run base noQuantum pair.modulus input count).code.resourcePool path) =
        8 * count * ((n + 1 + (n + 2) / 2) * (n + 1 + (n + 2) / 2 - 1) +
          ((n + 2) / 2) * ((n + 2) / 2 - 1)) := by
  rw [nativeOracle_finiteRetry_controlledPhase_count, firstBits_sameBit pair positive,
    ell_sameBit pair positive]
  exact phase_arithmetic count _ _

/-- The same bank's original two inverse QFTs retain their exact swap count. -/
theorem nativeOracle_finiteRetry_swap_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (input : Input pair.modulus) (count : Nat)
    (path : (run base noQuantum pair.modulus input count).code.Path) :
    ResourcePool.count qftSwapEvent
      ((run base noQuantum pair.modulus input count).code.resourcePool path) =
        16 * count * ((n + 1 + (n + 2) / 2) / 2 + ((n + 2) / 2) / 2) := by
  rw [nativeOracle_finiteRetry_swap_count, firstBits_sameBit pair positive,
    ell_sameBit pair positive]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite
