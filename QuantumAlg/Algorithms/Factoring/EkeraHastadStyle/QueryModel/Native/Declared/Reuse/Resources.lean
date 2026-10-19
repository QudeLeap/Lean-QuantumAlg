/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.Sample
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Bounds

/-!
# Actual declared sampling after paid reuse of the original bank

Every existing qubit is measured and receives its selected native correction.
Zero correction emits no gate; the independent allowance reserves at most one
X after each Z. The weighted allowance is a conservative total-work bound.
The following member retains its original parallel dependency expression for
arbitrary event durations. All per-wire lexical scratch bits are counted exactly.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

/-- The actual parent reset owns one classical measurement cell per original bank wire. -/
def resetSpace (N : Nat) : SpacePool .quantum :=
  ShortDLP.totalQubits (Native.parameters N) • SpacePool.ofShape (.finite 2)

/-- A nonempty bank has one selected correction layer; the empty bank has no work. -/
public def resetQuantumTime (N : Nat) : Nat :=
  if ShortDLP.totalQubits (Native.parameters N) = 0 then 0 else 1

variable {N : Nat}

/-- Each original bank wire reserves one Z and at most one native X correction. -/
def resetEventBudget (N : Nat) : ResourcePool (model N) :=
  ZReset.Bank.envelope (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (ShortDLP.totalQubits (Native.parameters N)) BitWord.model

/-- Reuse has no preparation event and keeps the original member allowance. -/
def reuseEventBudget (N : Nat) : ResourcePool (model N) :=
  resetEventBudget N + memberEventBudget N

/-- A total-work allowance reserves both actual native durations per bank wire. -/
def resetDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  ShortDLP.totalQubits (Native.parameters N) *
    (duration (.measurement (2 : ℕ+)) + duration (.gate .singleQubit))

/-- Reset precedes the original member's complete native dependency expression. -/
def reuseDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  resetDurationBudget N duration + memberDuration N duration

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat)

private lemma context_width :
    (Native.context base noQuantum N).systemCount =
      ShortDLP.totalQubits (Native.parameters N) := by
  have count := congrArg List.length (Native.nativeOracle_context_wires base noQuantum N)
  simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using count

/-- The actual scoped reset obeys the independent width allowance in the same declared model. -/
lemma declaredReuse_reset_resourcePool_le (path : (resetBank base noQuantum N).Path) :
    (resetBank base noQuantum N).resourcePool path ≤ resetEventBudget N := by
  have bounded := ZReset.BankParallel.code_eventEnvelope_le (services := .empty)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N))
    path
  exact bounded.trans_eq (congrArg
    (fun width => ZReset.Bank.envelope
      (oracles := ShortDLP.declaredModel N (Native.parameters N)) width BitWord.model)
    (context_width base noQuantum N))

/-- Zero corrections may be empty; every actual reset path has at most two events per qubit. -/
lemma declaredReuse_reset_eventTrace_length_le
    (path : (resetBank base noQuantum N).Path) :
    ((resetBank base noQuantum N).eventTrace path).length ≤
      2 * ShortDLP.totalQubits (Native.parameters N) := by
  exact (ZReset.BankParallel.code_eventTrace_length_le (services := .empty)
    (oracles := ShortDLP.declaredModel N (Native.parameters N))
    (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N))
    path).trans_eq (congrArg (2 * ·) (context_width base noQuantum N))

/-- Arbitrary native durations are bounded by the total work of the actual reset prefix. -/
lemma declaredReuse_reset_depth_le (duration : Resource.Event (model N) → Nat)
    (path : (resetBank base noQuantum N).Path) :
    (resetBank base noQuantum N).depth duration path ≤
      resetDurationBudget N duration := by
  refine (Circuit.depth_le_weightedCount_of_pool_le (resetBank base noQuantum N)
    duration (resetEventBudget N) path
    (declaredReuse_reset_resourcePool_le base noQuantum N path)).trans_eq ?_
  simp only [resetEventBudget, resetDurationBudget, ZReset.Bank.envelope, ZReset.eventEnvelope,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, Nat.one_mul]

/-- Actual reset and actual sampling share one complete declared-model event allowance. -/
lemma declaredReuse_resourcePool_le (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N parameter).Path) :
    (reuse base noQuantum N parameter).resourcePool path ≤ reuseEventBudget N := by
  change (resetBank base noQuantum N).resourcePool path.1 +
    (body base noQuantum N parameter).resourcePool path.2 ≤ _
  exact add_le_add (declaredReuse_reset_resourcePool_le base noQuantum N path.1)
    (declaredSample_body_resourcePool base noQuantum N parameter path.2).le

/-- The real selected reset prefix precedes the exact original member depth. -/
lemma declaredReuse_depth (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model N) → Nat)
    (path : (reuse base noQuantum N parameter).Path) :
    (reuse base noQuantum N parameter).depth duration path =
      (resetBank base noQuantum N).depth duration path.1 + memberDuration N duration := by
  exact (Circuit.depth_seq (resetBank base noQuantum N)
    (body base noQuantum N parameter) duration path.1 path.2).trans
      (congrArg ((resetBank base noQuantum N).depth duration path.1 + ·)
        (declaredSample_body_depth base noQuantum N parameter duration path.2))

/-- The original member's parallelism is retained in the arbitrary-duration reuse bound. -/
lemma declaredReuse_depth_le (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model N) → Nat)
    (path : (reuse base noQuantum N parameter).Path) :
    (reuse base noQuantum N parameter).depth duration path ≤
      reuseDurationBudget N duration := by
  rw [declaredReuse_depth]
  exact Nat.add_le_add_right (declaredReuse_reset_depth_le base noQuantum N duration path.1) _

/-- Actual reset time follows the single correction layer, including the empty case. -/
lemma declaredReuse_reset_quantumTime_le (path : (resetBank base noQuantum N).Path) :
    (resetBank base noQuantum N).quantumTime path ≤ resetQuantumTime N := by
  have bounded := ZReset.BankParallel.code_quantumTime_le_layer (services := .empty)
    (oracles := ShortDLP.declaredModel N (Native.parameters N)) (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)) path
  rw [context_width base noQuantum N] at bounded
  exact bounded

/-- Reset's single correction layer precedes the original complete member quantum time. -/
lemma declaredReuse_quantumTime_le (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N parameter).Path) :
    (reuse base noQuantum N parameter).quantumTime path ≤
      resetQuantumTime N + memberDuration N Resource.Event.quantumDuration := by
  change (reuse base noQuantum N parameter).depth Resource.Event.quantumDuration path ≤ _
  rw [declaredReuse_depth]
  exact Nat.add_le_add_right
    (declaredReuse_reset_quantumTime_le base noQuantum N path.1) _

/-- Every reset result cell is present together at the actual resident peak. -/
lemma declaredReuse_reset_peakResidentSpace
    (path : (resetBank base noQuantum N).Path) :
    (resetBank base noQuantum N).peakResidentSpace path =
      resetSpace N + (Native.context base noQuantum N).residentSpace := by
  have peak := ZReset.BankParallel.code_peakResidentSpace (services := .empty)
    (oracles := ShortDLP.declaredModel N (Native.parameters N)) (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)) path
  rw [context_width base noQuantum N] at peak
  exact peak

/-- Every reset result cell is charged at the actual auxiliary peak. -/
lemma declaredReuse_reset_peakAuxiliarySpace
    (path : (resetBank base noQuantum N).Path) :
    (resetBank base noQuantum N).peakAuxiliarySpace path =
      resetSpace N + (Native.context base noQuantum N).auxiliarySpace := by
  have peak := ZReset.BankParallel.code_peakAuxiliarySpace (services := .empty)
    (oracles := ShortDLP.declaredModel N (Native.parameters N)) (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N)) path
  rw [context_width base noQuantum N] at peak
  exact peak

/-- The only extra resident storage is the actual per-wire scratch group during reset. -/
lemma declaredReuse_peakResidentSpace (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N parameter).Path) :
    (reuse base noQuantum N parameter).peakResidentSpace path =
      resetSpace N + (Native.context base noQuantum N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (resetBank base noQuantum N) (body base noQuantum N parameter) path).trans ?_
  rw [declaredReuse_reset_peakResidentSpace, declaredSample_body_peakResidentSpace]
  exact SpacePool.max_eq_left (fun axis => Nat.le_add_left _ _)

/-- The same per-wire lexical allocation contributes once to the actual auxiliary peak. -/
lemma declaredReuse_peakAuxiliarySpace (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N parameter).Path) :
    (reuse base noQuantum N parameter).peakAuxiliarySpace path =
      resetSpace N + (Native.context base noQuantum N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (resetBank base noQuantum N) (body base noQuantum N parameter) path).trans ?_
  rw [declaredReuse_reset_peakAuxiliarySpace, declaredSample_body_peakAuxiliarySpace]
  exact SpacePool.max_eq_left (fun axis => Nat.le_add_left _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
