/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Measurements
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Count
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Gates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Counts
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters

/-!
# Native coordinates of the same actual measured RSA-2048 execution

Four complete configured batches execute eighty original members and all
2051 measured multiplications per member. Complete control feedback, physical
reset and actual literal loading are included in the independent native gate
ceilings below [G25, main.tex:199-295,354-360; EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA2048.Measured

noncomputable section

attribute [local instance] RSA.Configuration.rsa2048

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := ShortDLP.CompiledMAU.Recycling.model

/-- Separate original native gate allowances of the complete four-batch program. -/
def gateCountBound : AlgorithmGate.Coordinate → Nat
  | .toffoli => 19_254_517_596_160
  | .cnot => 74_265_936_855_040
  | .singleQubit => 16_506_186_343_601

/-- Every original arithmetic vent, control readout and full physical reset remains charged. -/
def measurementBound : Nat := 2_750_117_806_640

/-- Independent native quantum work is an upper bound on the actual dependency time. -/
def quantumTimeBound : Nat := 110_026_640_794_801

/-- The original complete native source, packing, recovery and selection allowance. -/
def classicalOperationBound : Nat := 13_881_799_957_336_389_973

private def arithmeticGateBound (width : Nat) : AlgorithmGate.Coordinate → Nat
  | .toffoli => 28 * width ^ 2 - 45 * width
  | .cnot => 108 * width ^ 2 - 178 * width
  | .singleQubit => 24 * width ^ 2 - 32 * width

private lemma rsaMeasured2048_round_gate_count (m ell width N : Nat)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate coordinate)
      (RSA.Measured.Program.roundEventBudget m ell width N) =
        ShortDLP.CompiledMAU.Recycling.resultBits m ell * arithmeticGateBound width coordinate +
        if coordinate = .singleQubit then
          3 * ShortDLP.CompiledMAU.Recycling.resultBits m ell +
            (ell + m).choose 2 + ell.choose 2 + (2 * width + 4) +
            EncodedBit.Word.BasisLoad.xCount
              (ShortDLP.CompiledMAU.Recycling.Measured.seedLabel width N)
        else 0 := by
  cases coordinate
  all_goals
    simp [RSA.Measured.Program.roundEventBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.Round.eventBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.Round.packingBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.BankReset.eventBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.Resources.memberBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.Resources.baseBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.Resources.arithmeticBudget,
      ShortDLP.CompiledMAU.Recycling.Measured.Resources.oneQubit,
      ShortDLP.CompiledMAU.Recycling.Measured.Resources.oneMeasurement,
      MAU.Multiplication.Gidney.Measured.Layout.multiplicationBudget,
      MAU.Addition.Gidney.Measured.Instruction.coordinatePool, arithmeticGateBound]
  all_goals ring

private lemma rsaMeasured2048_four_gate_count (N : Nat) (coordinate : AlgorithmGate.Coordinate) :
    RSA.Measured.Program.gateCountLimit N 4 coordinate =
      80 * ResourcePool.count (model := Model) (.gate coordinate)
        (RSA.Measured.Program.roundEventBudget
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) +
      if coordinate = .singleQubit then
        EncodedBit.Word.BasisLoad.xCount
          (ShortDLP.CompiledMAU.Recycling.Measured.seedLabel (arithmeticBits N) N)
      else 0 := by
  have sourceZero := RecoveryNativeGates.sampler_gate_zero (model := Model) coordinate N
  have recoveryZero := RecoveryNativeGates.recovery_gate_zero (model := Model) coordinate N 18
  have selectionZero := RecoveryNativeGates.optional_gate_zero
    (model := Model) coordinate (modulusBits N) 4
  have configuredAdditional : RSA.Configuration.additionalMembers = 18 := rfl
  simp only [RSA.Measured.Program.gateCountLimit, RSA.Measured.Program.eventBudget,
    RSA.Measured.Program.batchEventBudget, RSA.Measured.Program.bodyEventBudget,
    RSA.Measured.Program.sourceEventBudget, RSA.Measured.Program.recoveryEventBudget,
    RSA.Measured.Program.selectionEventBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, RSA.membersPerBatch, configuredAdditional,
    sourceZero, recoveryZero, selectionZero, zero_add, add_zero]
  cases coordinate <;>
    simp [RSA.Measured.Program.preparationEventBudget, RSA.Measured.Program.seedEventBudget]
    <;> ring

/-- The complete actual program's independent gate allowance has exactly these three values. -/
lemma rsaMeasured2048_model_gateCountLimit_eq {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (coordinate : AlgorithmGate.Coordinate) :
    RSA.Measured.Program.gateCountLimit N RSA.Configuration.rsa2048Batches coordinate =
      gateCountBound coordinate := by
  have nontrivial : 1 < N := by
    rw [model.modulus_eq]
    exact (inputOfKeyPair model.pair).modulus_gt_one
  have loader := ShortDLP.CompiledMAU.Recycling.Measured.measuredSeed_xCount
    2048 N (by decide) nontrivial
  have width := NativeRSA2048.model_arithmeticBits_eq model
  norm_num only [NativeRSA2048.modulusBits, NativeRSA2048.primeBits] at width
  rw [RSA.Configuration.rsa2048Batches, rsaMeasured2048_four_gate_count,
    rsaMeasured2048_round_gate_count, NativeRSA2048.model_shortLogBits_eq model,
    NativeRSA2048.model_tradeoffBits_eq model, width, loader]
  cases coordinate with
  | toffoli =>
      have different : AlgorithmGate.Coordinate.toffoli ≠ .singleQubit := by
        intro impossible
        cases impossible
      norm_num [arithmeticGateBound, gateCountBound, different,
        ShortDLP.CompiledMAU.Recycling.resultBits, NativeRSA2048.primeBits, Nat.choose_two_right]
  | cnot =>
      have different : AlgorithmGate.Coordinate.cnot ≠ .singleQubit := by
        intro impossible
        cases impossible
      norm_num [arithmeticGateBound, gateCountBound, different,
        ShortDLP.CompiledMAU.Recycling.resultBits, NativeRSA2048.primeBits, Nat.choose_two_right]
  | singleQubit =>
      norm_num [arithmeticGateBound, gateCountBound,
        ShortDLP.CompiledMAU.Recycling.resultBits, NativeRSA2048.primeBits, Nat.choose_two_right]

/-- Main arithmetic Toffolis are exactly the requested eighty times 2051 width-only allowance. -/
lemma rsaMeasured2048_main_toffoli_allowance :
    80 * 2051 * (28 * 2048 ^ 2 - 45 * 2048) = gateCountBound .toffoli := by
  norm_num [gateCountBound]

private lemma rsaMeasured2048_quantumWork_gateCounts (pool : ResourcePool Model) :
    ResourcePool.weightedCount Resource.Event.quantumDuration pool =
      ResourcePool.count (model := Model) (.gate .toffoli) pool +
        ResourcePool.count (model := Model) (.gate .cnot) pool +
        ResourcePool.count (model := Model) (.gate .singleQubit) pool := by
  induction pool using Multiset.induction_on with
  | empty => rfl
  | cons event rest ih =>
      have oneEvent : Resource.Event.quantumDuration event =
          ResourcePool.count (model := Model) (.gate .toffoli)
              (ResourcePool.singleton (model := Model) event) +
            ResourcePool.count (model := Model) (.gate .cnot)
              (ResourcePool.singleton (model := Model) event) +
              ResourcePool.count (model := Model) (.gate .singleQubit)
                (ResourcePool.singleton (model := Model) event) := by
        cases event with
        | gate coordinate => cases coordinate <;> simp [ResourcePool.count_singleton]
        | oracle coordinate => exact nomatch coordinate
        | classicalQuery coordinate => exact nomatch coordinate
        | classicalOperation _ => simp [ResourcePool.count_singleton]
        | preparation _ => simp [ResourcePool.count_singleton]
        | measurement _ => simp [ResourcePool.count_singleton]
      have splitPool : event ::ₘ rest = ResourcePool.singleton (model := Model) event + rest := rfl
      rw [splitPool, ResourcePool.weightedCount_add, ResourcePool.weightedCount_singleton,
        ResourcePool.count_add, ResourcePool.count_add, ResourcePool.count_add, ih, Nat.one_mul,
        oneEvent]
      omega

/-- The same independent native allowance bounds the actual quantum schedule by this value. -/
lemma rsaMeasured2048_model_quantumTimeLimit_eq {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Measured.Program.quantumTimeLimit N RSA.Configuration.rsa2048Batches =
      quantumTimeBound := by
  unfold RSA.Measured.Program.quantumTimeLimit
  rw [rsaMeasured2048_quantumWork_gateCounts]
  change RSA.Measured.Program.gateCountLimit N RSA.Configuration.rsa2048Batches .toffoli +
      RSA.Measured.Program.gateCountLimit N RSA.Configuration.rsa2048Batches .cnot +
      RSA.Measured.Program.gateCountLimit N RSA.Configuration.rsa2048Batches .singleQubit = _
  rw [rsaMeasured2048_model_gateCountLimit_eq model,
    rsaMeasured2048_model_gateCountLimit_eq model, rsaMeasured2048_model_gateCountLimit_eq model]
  norm_num [gateCountBound, quantumTimeBound]

private lemma rsaMeasured2048_classicalWeight_le_card (pool : ResourcePool Model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bound := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event Model => 1) (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bound

private lemma rsaMeasured2048_round_classicalWeight (m ell width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (RSA.Measured.Program.roundEventBudget m ell width N) = 1 := by
  simp [RSA.Measured.Program.roundEventBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Round.eventBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Round.packingBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.BankReset.eventBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.memberBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.baseBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.arithmeticBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.oneQubit,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.oneMeasurement,
    MAU.Multiplication.Gidney.Measured.Layout.multiplicationBudget,
    MAU.Addition.Gidney.Measured.Instruction.coordinatePool,
    Resource.Event.classicalOperationWeight]

private lemma rsaMeasured2048_four_classicalWeight (N : Nat) :
    RSA.Measured.Program.classicalOperationLimit N 4 ≤
      4 * (44 * modulusBits N + 186 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) 18) + 1 := by
  have sourceBound := (rsaMeasured2048_classicalWeight_le_card
    (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N)).trans_eq
      (ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card Model N)
  have recoveryBound := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
    (model := Model) N 18
  unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width at recoveryBound
  have selectionBound := (rsaMeasured2048_classicalWeight_le_card
    (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) 4)).trans_eq
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope_card Model (modulusBits N) 4)
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N) ≤
        44 * modulusBits N + 163 at sourceBound
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) 4) ≤
        13 at selectionBound
  simp only [RSA.Measured.Program.classicalOperationLimit, RSA.Measured.Program.eventBudget,
    RSA.Measured.Program.batchEventBudget, RSA.Measured.Program.bodyEventBudget,
    RSA.Measured.Program.sourceEventBudget, RSA.Measured.Program.recoveryEventBudget,
    RSA.Measured.Program.selectionEventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, rsaMeasured2048_round_classicalWeight]
  simp only [RSA.Measured.Program.preparationEventBudget, RSA.Measured.Program.seedEventBudget,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.classicalOperationWeight, mul_zero, zero_add]
  change 4 * (ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N) +
        (20 + ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := Model) N 18))) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) 4) ≤
      4 * (44 * modulusBits N + 186 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) 18) + 1
  calc
    _ ≤ 4 * ((44 * modulusBits N + 163) +
        (20 + LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) 18)) + 13 :=
      Nat.add_le_add (Nat.mul_le_mul_left 4
        (Nat.add_le_add sourceBound (Nat.add_le_add_left recoveryBound 20))) selectionBound
    _ = _ := by ring

/-- The full classical-only ceiling evaluates the unchanged recovery width formula. -/
lemma rsaMeasured2048_model_classicalOperationLimit_le {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Measured.Program.classicalOperationLimit N RSA.Configuration.rsa2048Batches ≤
      classicalOperationBound := by
  refine (rsaMeasured2048_four_classicalWeight N).trans_eq ?_
  rw [NativeRSA2048.model_coordinateWidth_eq model,
    NativeRSA2048.model_modulusBits_eq model, NativeRSA2048.model_shortLogBits_eq model,
    NativeRSA2048.model_tradeoffBits_eq model]
  change 4 * (44 * 2_048 + 186 + LatticeFixedBatchRecoveryMachine.eventCountBound
    2_048 1_025 513 7_522_484_226 18) + 1 = classicalOperationBound
  norm_num [LatticeFixedBatchRecoveryMachine.eventCountBound,
    LatticeFixedBatchRecoveryMachine.nearestPlaneEnvelopeBound, RSA.shortLogRecoveryFuel,
    LatticeRecoveryResources.modularSetupCardBound, LatticeRecoveryResources.candidateScanCardBound,
    LatticeRecoveryResources.candidateScanWork, LatticeRecoveryResources.candidateSlotCardBound,
    LatticeRecoveryResources.quadraticGuardedCardBound, LatticeRecoveryResources.natSqrtCardBound,
    QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth,
    classicalOperationBound, Nat.choose_two_right]

private lemma rsaMeasured2048_four_measurement_count (N : Nat) :
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+))
      (RSA.Measured.Program.eventBudget N 4) =
      80 * (ShortDLP.CompiledMAU.Recycling.resultBits (shortLogBits N) (tradeoffBits N) *
        (4 * arithmeticBits N * (arithmeticBits N - 2) + 1) + (2 * arithmeticBits N + 4)) := by
  have sourceZero := RSA.Measured.Program.Measurements.rsaMeasuredClassical_sampler_measurement_zero
    (model := Model) (2 : ℕ+) N
  have recoveryZero :=
    RSA.Measured.Program.Measurements.rsaMeasuredClassical_recovery_measurement_zero
      (model := Model) (2 : ℕ+) N 18
  have selectionZero :=
    RSA.Measured.Program.Measurements.rsaMeasuredClassical_optional_measurement_zero
      (model := Model) (2 : ℕ+) (modulusBits N) 4
  have configuredAdditional : RSA.Configuration.additionalMembers = 18 := rfl
  simp only [RSA.Measured.Program.eventBudget,
    RSA.Measured.Program.batchEventBudget, RSA.Measured.Program.bodyEventBudget,
    RSA.Measured.Program.sourceEventBudget, RSA.Measured.Program.recoveryEventBudget,
    RSA.Measured.Program.selectionEventBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, RSA.membersPerBatch, configuredAdditional,
    sourceZero, recoveryZero, selectionZero, zero_add, add_zero]
  simp [RSA.Measured.Program.preparationEventBudget, RSA.Measured.Program.seedEventBudget,
    RSA.Measured.Program.roundEventBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Round.eventBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Round.packingBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.BankReset.eventBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.memberBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.baseBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.arithmeticBudget,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.oneQubit,
    ShortDLP.CompiledMAU.Recycling.Measured.Resources.oneMeasurement,
    MAU.Multiplication.Gidney.Measured.Layout.multiplicationBudget,
    MAU.Addition.Gidney.Measured.Instruction.coordinatePool]
  ring

/-- The full physical measurement allowance is a separate coordinate of the same real program. -/
lemma rsaMeasured2048_model_measurementLimit_eq {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) :
    ResourcePool.count (model := Model) (.measurement (2 : ℕ+))
      (RSA.Measured.Program.eventBudget N RSA.Configuration.rsa2048Batches) =
        measurementBound := by
  rw [RSA.Configuration.rsa2048Batches, rsaMeasured2048_four_measurement_count,
    NativeRSA2048.model_shortLogBits_eq model, NativeRSA2048.model_tradeoffBits_eq model,
    NativeRSA2048.model_arithmeticBits_eq model]
  norm_num [measurementBound, ShortDLP.CompiledMAU.Recycling.resultBits,
    NativeRSA2048.modulusBits, NativeRSA2048.primeBits]

end

end QuantumAlg.Factoring.RSA2048.Measured
