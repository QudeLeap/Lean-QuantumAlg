/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.Sample
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Actual declared sampling after paid reuse of the original bank

Every existing qubit is measured and receives its selected native correction.
Zero correction emits no gate; the independent allowance reserves at most one
X after each Z. Only this serial reset prefix uses its weighted allowance.
The following member retains its original parallel dependency expression for
arbitrary event durations. The one lexical scratch bit is counted exactly.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

variable {N : Nat}

/-- Each original bank wire reserves one Z and at most one native X correction. -/
def resetEventBudget (input : Input N) : ResourcePool (model input) :=
  ZReset.Bank.envelope (oracles := ShortDLP.declaredModel (Native.encoding input))
    (ShortDLP.totalQubits (Native.parameters N)) BitWord.model

/-- Reuse has no preparation event and keeps the original member allowance. -/
def reuseEventBudget (input : Input N) : ResourcePool (model input) :=
  resetEventBudget input + memberEventBudget input

/-- The serial reset prefix reserves the two actual native durations per bank wire. -/
def resetDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  ShortDLP.totalQubits (Native.parameters N) *
    (duration (.measurement (2 : ℕ+)) + duration (.gate .singleQubit))

/-- Reset precedes the original member's complete native dependency expression. -/
def reuseDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  resetDurationBudget input duration + memberDuration input duration

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private theorem context_width :
    (Native.context base noQuantum N).systemCount =
      ShortDLP.totalQubits (Native.parameters N) := by
  have count := congrArg List.length (Native.nativeOracle_context_wires base noQuantum N)
  simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using count

/-- The actual scoped reset obeys the independent width allowance in the same declared model. -/
theorem declaredReuse_reset_resourcePool_le (path : (resetBank base noQuantum N input).Path) :
    (resetBank base noQuantum N input).resourcePool path ≤ resetEventBudget input := by
  have bounded := ZReset.BankScope.zResetBankScope_resourcePool_le
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N))
    path
  exact bounded.trans_eq (congrArg
    (fun width => ZReset.Bank.envelope
      (oracles := ShortDLP.declaredModel (Native.encoding input)) width BitWord.model)
    (context_width base noQuantum N))

/-- Zero corrections may be empty; every actual reset path has at most two events per qubit. -/
theorem declaredReuse_reset_eventTrace_length_le
    (path : (resetBank base noQuantum N input).Path) :
    ((resetBank base noQuantum N input).eventTrace path).length ≤
      2 * ShortDLP.totalQubits (Native.parameters N) := by
  exact (ZReset.BankScope.zResetBankScope_eventTrace_length_le
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N))
    path).trans_eq (congrArg (2 * ·) (context_width base noQuantum N))

/-- Arbitrary native durations charge the actual serial reset prefix before reuse. -/
theorem declaredReuse_reset_depth_le (duration : Resource.Event (model input) → Nat)
    (path : (resetBank base noQuantum N input).Path) :
    (resetBank base noQuantum N input).depth duration path ≤
      resetDurationBudget input duration := by
  refine (Circuit.depth_le_weightedCount_of_pool_le (resetBank base noQuantum N input)
    duration (resetEventBudget input) path
    (declaredReuse_reset_resourcePool_le base noQuantum N input path)).trans_eq ?_
  simp only [resetEventBudget, resetDurationBudget, ZReset.Bank.envelope, ZReset.eventEnvelope,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, Nat.one_mul]

/-- Actual reset and actual sampling share one complete declared-model event allowance. -/
theorem declaredReuse_resourcePool_le (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).resourcePool path ≤ reuseEventBudget input := by
  change (resetBank base noQuantum N input).resourcePool path.1 +
    (body base noQuantum N input parameter).resourcePool path.2 ≤ _
  exact add_le_add (declaredReuse_reset_resourcePool_le base noQuantum N input path.1)
    (declaredSample_body_resourcePool base noQuantum N input parameter path.2).le

/-- The real selected reset prefix precedes the exact original member depth. -/
theorem declaredReuse_depth (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model input) → Nat)
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).depth duration path =
      (resetBank base noQuantum N input).depth duration path.1 + memberDuration input duration := by
  exact (Circuit.depth_seq (resetBank base noQuantum N input)
    (body base noQuantum N input parameter) duration path.1 path.2).trans
      (congrArg ((resetBank base noQuantum N input).depth duration path.1 + ·)
        (declaredSample_body_depth base noQuantum N input parameter duration path.2))

/-- The original member's parallelism is retained in the arbitrary-duration reuse bound. -/
theorem declaredReuse_depth_le (parameter : CInputRef base (ParameterShape N))
    (duration : Resource.Event (model input) → Nat)
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).depth duration path ≤
      reuseDurationBudget input duration := by
  rw [declaredReuse_depth]
  exact Nat.add_le_add_right (declaredReuse_reset_depth_le base noQuantum N input duration path.1) _

/-- The only extra resident storage is the one actual finite scratch cell during reset. -/
theorem declaredReuse_peakResidentSpace (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).peakResidentSpace path =
      SpacePool.ofShape (.finite 2) + (Native.context base noQuantum N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq (resetBank base noQuantum N input)
    (body base noQuantum N input parameter) path).trans ?_
  rw [declaredSample_body_peakResidentSpace]
  have reset := ZReset.BankScope.zResetBankScope_peakResidentSpace
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N))
    path.1
  refine (congrArg (fun value => SpacePool.max value
    (Native.context base noQuantum N).residentSpace) reset).trans ?_
  apply SpacePool.ext
  intro axis
  exact max_eq_left (Nat.le_add_left _ _)

/-- The same one-bit lexical allocation contributes once to the actual auxiliary peak. -/
theorem declaredReuse_peakAuxiliarySpace (parameter : CInputRef base (ParameterShape N))
    (path : (reuse base noQuantum N input parameter).Path) :
    (reuse base noQuantum N input parameter).peakAuxiliarySpace path =
      SpacePool.ofShape (.finite 2) + (Native.context base noQuantum N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (resetBank base noQuantum N input)
    (body base noQuantum N input parameter) path).trans ?_
  rw [declaredSample_body_peakAuxiliarySpace]
  have reset := ZReset.BankScope.zResetBankScope_peakAuxiliarySpace
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Native.nativeOracle_context_wires base noQuantum N))
    path.1
  refine (congrArg (fun value => SpacePool.max value
    (Native.context base noQuantum N).auxiliarySpace) reset).trans ?_
  apply SpacePool.ext
  intro axis
  exact max_eq_left (Nat.le_add_left _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
