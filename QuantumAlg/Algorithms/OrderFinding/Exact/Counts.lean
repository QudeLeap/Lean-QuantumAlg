/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Context
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Components.Classical.TerminalDecode.Counts
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Core.Execution.Trace

/-!
# Exact native quantum counts after actual classical decoding

The real decoder emits only word shifts and selected increments. Its proved
coordinatewise envelope therefore adds no quantum query or gate to the
original sample. These exact counts concern the same complete execution.
-/

namespace QuantumAlg.OrderFinding.Exact

noncomputable section

private theorem decoder_queryCount (t n : Nat) (label : Resource.QuantumSubroutineLabel)
    (path : (decoderCode t n).Path) :
    ResourcePool.count (.quantumSubroutine label) ((decoderCode t n).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
      path) (.quantumSubroutine label)
  have zero : ResourcePool.count (.quantumSubroutine label)
      ((decoderCode t n).resourcePool path) ≤ 0 := by
    simpa [decoderCode, ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent] using bounded
  exact Nat.eq_zero_of_le_zero zero

private theorem decoder_gateCount (t n : Nat) (label : Resource.GateLabel)
    (path : (decoderCode t n).Path) :
    ResourcePool.count (.gate label) ((decoderCode t n).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n)
      path) (.gate label)
  have zero : ResourcePool.count (.gate label) ((decoderCode t n).resourcePool path) ≤ 0 := by
    simpa [decoderCode, ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent] using bounded
  exact Nat.eq_zero_of_le_zero zero

/-- Exactly one modular-exponentiation query belongs to every complete native sample. -/
theorem code_modExpCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) :
    ResourcePool.count (modExpEvent N x t n) ((code A).resourcePool path) = 1 := by
  change ResourcePool.count (modExpEvent N x t n) (ResourcePool.ofList
    ((Sampling.code A).eventTrace path.1 ++ (decoderCode t n).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (modExpEvent N x t n) ((Sampling.code A).resourcePool path.1) +
    ResourcePool.count (.quantumSubroutine (modExpSubroutineLabel N x t n).quantum)
      ((decoderCode t n).resourcePool path.2) = _
  rw [Sampling.code_modExpCount, decoder_queryCount, Nat.add_zero]

/-- Complete decoding leaves every exact native quantum-gate coordinate unchanged. -/
theorem code_gateCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) (label : Resource.GateLabel) :
    ResourcePool.count (.gate label) ((code A).resourcePool path) =
      ResourcePool.count (.gate label) (Sampling.unitaryEventBudget N x t n) := by
  change ResourcePool.count (.gate label) (ResourcePool.ofList
    ((Sampling.code A).eventTrace path.1 ++ (decoderCode t n).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (.gate label) ((Sampling.code A).resourcePool path.1) +
    ResourcePool.count (.gate label) ((decoderCode t n).resourcePool path.2) = _
  rw [decoder_gateCount, Nat.add_zero, Sampling.code_events]
  simp [Sampling.eventBudget, Sampling.basisPreparationEvent]

/-- Exact Hadamard, controlled-phase and SWAP multiplicities of the complete algorithm. -/
theorem code_quantumGateCounts {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) :
    ResourcePool.count (.gate (.builtin "hadamard")) ((code A).resourcePool path) = 2 * t ∧
      ResourcePool.count (.gate qftControlledPhaseLabel) ((code A).resourcePool path) =
        t * (t - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap")) ((code A).resourcePool path) = t / 2 := by
  simp [code_gateCount, Sampling.unitaryEventBudget, modExpEvent,
    WalshHadamard.hadamardEvent, qftControlledPhaseLabel, Nat.choose_two_right,
    two_mul, Resource.GateLabel.controlForDimension, Resource.GateLabel.builtin,
    Resource.GateLabel.controlForDimensions, Resource.GateLabel.declared]

/-- The real materialization performs exactly one shift for each actual packed source bit. -/
theorem code_shiftCount {N x t n : Nat} (A : ModExpOracleAccess N x t n)
    (path : (code A).Path) :
    ResourcePool.count (ClassicalRoutines.TerminalDecode.shiftEvent t)
      ((code A).resourcePool path) = t := by
  let event : Resource.Event .quantum :=
    ClassicalRoutines.TerminalDecode.shiftEvent t
  change ResourcePool.count event (ResourcePool.ofList
    ((Sampling.code A).eventTrace path.1 ++ (decoderCode t n).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count event ((Sampling.code A).resourcePool path.1) +
    ResourcePool.count event ((decoderCode t n).resourcePool path.2) = _
  have sampling : ResourcePool.count event ((Sampling.code A).resourcePool path.1) = 0 := by
    rw [Sampling.code_events]
    simp [event, ClassicalRoutines.TerminalDecode.shiftEvent,
      Sampling.eventBudget, Sampling.unitaryEventBudget, Sampling.basisPreparationEvent,
      modExpEvent, WalshHadamard.hadamardEvent]
  have decoding : ResourcePool.count event ((decoderCode t n).resourcePool path.2) = t :=
    ClassicalRoutines.TerminalDecode.terminalDecode_routine_shiftCount
      (Sampling.post t n) t .bigEndian (packedInput t n) (resultKey t n) (resultFresh t n) path.2
  rw [sampling, decoding, Nat.zero_add]

end

end QuantumAlg.OrderFinding.Exact
