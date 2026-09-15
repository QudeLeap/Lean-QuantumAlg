/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Events
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Counts
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Closed scalar counts for the complete native finite retry

The width formulas bound the independent coordinate allowance of the same
complete execution. They retain all measured-round coordinates, all 120
recovery pairs, and the selector's literal classical instructions. Envelope
cardinality may exceed any chosen path's event count because unselected
branch coordinates remain part of the allowance.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent width ceiling for all native events, including preparation and final packing. -/
def scalarEventCountBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 166 +
        16 * RuntimeRound.eventCountWidthBound
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 2

/-- Independent ceiling for literal classical operations; quantum preparation has zero weight. -/
def scalarClassicalOperationBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 182 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 1

/-- The complete existing coordinate allowance admits the closed scalar event ceiling. -/
theorem eventCountBound_le_scalar (N totalRounds : Nat) :
    eventCountBound N totalRounds ≤ scalarEventCountBound N totalRounds := by
  cases totalRounds with
  | zero => exact Nat.le_refl 0
  | succ count =>
    have measured := RuntimeRound.eventCountBound_le_widthBound
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    rw [← RuntimeRound.eventEnvelope_card] at measured
    have recovered := LatticeFixedBatchRecoveryMachine.eventEnvelope_card_le
      (kind := .quantum) N
    have batch := Nat.add_le_add (Nat.mul_le_mul_left 16 measured) recovered
    have repeated := Nat.mul_le_mul_left (count + 1) (Nat.add_le_add_left batch
      (44 * modulusBits N + 166))
    simpa only [eventCountBound, scalarEventCountBound,
      LatticePairCandidateRecovery.Width, LatticeWideLllMachine.Width, Nat.add_assoc] using
      Nat.add_le_add_right repeated 2

private theorem sampler_classicalWeight_le (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N) ≤
      44 * modulusBits N + 163 := by
  have weighted := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event .quantum => 1)
    (s := ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const',
    Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one,
    ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card, modulusBits] using weighted

/-- Every repeated classical instruction obeys the closed scalar ceiling for every batch count. -/
theorem classicalOperationBound_le_scalar (N totalRounds : Nat) :
    classicalOperationBound N totalRounds ≤ scalarClassicalOperationBound N totalRounds := by
  cases totalRounds with
  | zero => exact Nat.le_refl 0
  | succ count =>
    have sampler := sampler_classicalWeight_le N
    have recovery := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
      (kind := .quantum) N
    unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width at recovery
    have batch : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (NativeBatchReuseRecovery.eventEnvelope N) ≤
        44 * modulusBits N + 179 +
          LatticeFixedBatchRecoveryMachine.eventCountBound
            (modulusBits N) (shortLogBits N) (tradeoffBits N)
            (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) := by
      simp only [NativeBatchReuseRecovery.eventEnvelope, NativeBatchReuse.nativeEnvelope,
        ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
        RuntimeRound.eventEnvelope_classicalWeight, Nat.mul_one]
      omega
    have repeated := Nat.mul_le_mul_left (count + 1) batch
    unfold classicalOperationBound scalarClassicalOperationBound
    nlinarith

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Every complete actual run path satisfies the independent width-only native event ceiling. -/
theorem run_eventCount_le_widthBound (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    ((run base noQuantum input totalRounds).code.eventTrace path).length ≤
      scalarEventCountBound N totalRounds :=
  (run_eventCount_le_scalar base noQuantum input totalRounds path).trans
    (eventCountBound_le_scalar N totalRounds)

/-- Every literal classical operation is charged on that same complete actual run path. -/
theorem run_classicalOperation_le_widthBound (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum input totalRounds).code.resourcePool path) ≤
      scalarClassicalOperationBound N totalRounds :=
  (run_classicalOperation_le base noQuantum input totalRounds path).trans
    (classicalOperationBound_le_scalar N totalRounds)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
