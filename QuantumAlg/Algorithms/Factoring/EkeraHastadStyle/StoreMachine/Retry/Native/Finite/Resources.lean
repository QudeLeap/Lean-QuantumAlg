/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Accounting.Space
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Resources

/-!
# Independent budgets for every finite total batch count

The zero branch allocates its real empty optional result, with zero events
and zero event depth. A positive count uses the existing independent selected
chain budgets. Each bound applies to a path of the same actual finite code
or complete run. Temporary quantum capacity is independent of positive count.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent native events distinguish actual zero batches and positive selected chains. -/
public def eventEnvelope (N : Nat) : Nat →
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model)
  | 0 => 0
  | count + 1 => NativeRetrySelection.eventEnvelope N count

/-- Independent serial duration is zero for empty allocation and includes every positive batch. -/
public def depthBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => NativeRetrySelection.depthBound N count

/-- The real output cell is always charged, with positive-count scratch bounded by actual peaks. -/
public def additionalSpace (N : Nat) : Nat → SpacePool .quantum
  | 0 => NativeRetryEmpty.additionalSpace N
  | count + 1 => NativeRetrySelection.additionalSpace N count

/-- Zero requested batches have no independent native events. -/
lemma eventEnvelope_zero (N : Nat) : eventEnvelope N 0 = 0 := rfl

/-- Positive requested batches use exactly the original selected-chain ledger. -/
lemma eventEnvelope_positive (N count : Nat) :
    eventEnvelope N (count + 1) = NativeRetrySelection.eventEnvelope N count := rfl

/-- Empty-result allocation has no native event duration. -/
lemma depthBound_zero (N : Nat) : depthBound N 0 = 0 := rfl

/-- Positive-count serial duration is exactly the existing selected-chain formula. -/
lemma depthBound_succ (N count : Nat) :
    depthBound N (count + 1) = NativeRetrySelection.depthBound N count := rfl

/-- Zero batches still charge the actual retained optional-result capacity. -/
lemma additionalSpace_zero (N : Nat) :
    additionalSpace N 0 = NativeRetryEmpty.additionalSpace N := rfl

/-- Positive counts charge their complete retained layout and one actual temporary peak. -/
lemma additionalSpace_succ (N count : Nat) :
    additionalSpace N (count + 1) = NativeRetrySelection.additionalSpace N count := rfl

/-- The empty-result branch adds no quantum capacity. -/
lemma additionalSpace_zero_quantum (N : Nat) (dimension : ℕ+) :
    additionalSpace N 0 (.quantumSystems dimension) = 0 := rfl

/-- All positive batch counts share the same quantum peak allowance as one batch. -/
lemma additionalSpace_succ_quantum (N count : Nat) (dimension : ℕ+) :
    additionalSpace N (count + 1) (.quantumSystems dimension) =
      additionalSpace N 1 (.quantumSystems dimension) :=
  NativeRetrySelection.additionalSpace_quantum N count dimension

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every path of the actual finite code satisfies the independent native event budget. -/
lemma code_pool_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).resourcePool path ≤ eventEnvelope N totalRounds := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_pool base N path).le
  | succ count => exact NativeRetrySelection.code_pool_le base noQuantum input count path

/-- The same actual finite path obeys the independent native operation-count budget. -/
lemma code_eventCount_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    ((code base noQuantum input totalRounds).eventTrace path).length ≤
      (eventEnvelope N totalRounds).card :=
  Multiset.card_le_card (code_pool_le base noQuantum input totalRounds path)

/-- Native dependency depth follows the same zero or positive actual execution branch. -/
lemma code_depth_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).depth (fun _ => 1) path ≤ depthBound N totalRounds := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_depth base N (fun _ => 1) path).le
  | succ count => exact NativeRetrySelection.code_depth_le base noQuantum input count path

/-- The actual finite resident peak includes the caller and every branch's real allocation. -/
lemma code_resident_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).peakResidentSpace path ≤
      base.residentSpace + additionalSpace N totalRounds := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_resident base N path).le
  | succ count => exact NativeRetrySelection.code_resident_le base noQuantum input count path

/-- The same actual finite path includes its real retained and temporary auxiliary capacity. -/
lemma code_auxiliary_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N totalRounds := by
  cases totalRounds with
  | zero => exact (NativeRetryEmpty.code_auxiliary base N path).le
  | succ count => exact NativeRetrySelection.code_auxiliary_le base noQuantum input count path

/-- Every complete run path has the same actual native ledger as the selected finite code. -/
lemma run_pool_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.resourcePool path ≤
      eventEnvelope N totalRounds := by
  cases totalRounds with
  | zero => exact code_pool_le base noQuantum input 0 path
  | succ count => exact code_pool_le base noQuantum input (count + 1) path

/-- The complete actual run's native operation count satisfies the same independent budget. -/
lemma run_eventCount_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    ((run base noQuantum input totalRounds).code.eventTrace path).length ≤
      (eventEnvelope N totalRounds).card :=
  Multiset.card_le_card (run_pool_le base noQuantum input totalRounds path)

/-- The complete actual run has the same serial event-depth budget. -/
lemma run_depth_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.depth (fun _ => 1) path ≤
      depthBound N totalRounds := by
  cases totalRounds with
  | zero => exact code_depth_le base noQuantum input 0 path
  | succ count => exact code_depth_le base noQuantum input (count + 1) path

/-- Every complete run path has a canonical quantum-time bound from an independent full-run ceiling.
The same actual run includes its initial seed, every reused batch, reset and reload. -/
lemma run_quantumTime_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.quantumTime path ≤
      depthBound N totalRounds :=
  (Circuit.quantumTime_le_unitDepth _ path).trans
    (run_depth_le base noQuantum input totalRounds path)

/-- The complete actual run preserves the finite code's resident peak accounting. -/
lemma run_resident_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.peakResidentSpace path ≤
      base.residentSpace + additionalSpace N totalRounds := by
  cases totalRounds with
  | zero => exact code_resident_le base noQuantum input 0 path
  | succ count => exact code_resident_le base noQuantum input (count + 1) path

/-- The complete actual run preserves the finite code's auxiliary peak accounting. -/
lemma run_auxiliary_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.peakAuxiliarySpace path ≤
      base.auxiliarySpace + additionalSpace N totalRounds := by
  cases totalRounds with
  | zero => exact code_auxiliary_le base noQuantum input 0 path
  | succ count => exact code_auxiliary_le base noQuantum input (count + 1) path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
