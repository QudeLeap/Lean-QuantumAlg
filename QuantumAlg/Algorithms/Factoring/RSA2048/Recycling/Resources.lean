/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.QuantumTime
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Gates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.ResourceBounds
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.BankReset
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Stage
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Registers
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Stages
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum

/-!
# Fixed native budgets for the actual single-control RSA-2048 execution

The same complete seven-batch execution has 112 measured members. These are
scalar upper bounds of its independent parameter-only event and time pools.
The arithmetic pool uses independent CNOT and Toffoli allowances of the actual
pushed-control stage and its zero single-qubit count. All measured control corrections,
complete bank resets, reloads, paid packing, recovery and selection are kept.
Only a pure recovery-width evaluation is reused from the earlier fixed-width
module; none of its full-bank execution resource theorems is used here.
-/

namespace QuantumAlg.Factoring.RSA2048.Recycling

noncomputable section

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := ShortDLP.CompiledMAU.Recycling.model

/-- The unchanged serial selected multiplier has this independent quantum-time allowance. -/
def selectedStageTimeBound : Nat := 511_424_993_280

/-- Independent CNOT allowance of the actual pushed-control stage. -/
def selectedStageCnotBound : Nat := 1_812_234_240

/-- Independent Toffoli allowance of the same pushed-control stage. -/
def selectedStageToffoliBound : Nat := 509_612_759_040

/-- All previous-bit phases in both chronological exponent streams. -/
def feedbackPhaseBound : Nat := 1_313_281

/-- Sequential quantum time of one measured member, before its final bank reset and reload. -/
def measuredMemberTimeBound : Nat := 1_048_932_662_536_714

/-- Separate native ceilings include all 112 members, corrections, resets and reloads. -/
def gateCountBound : AlgorithmGate.Coordinate → Nat
  | .toffoli => 117_064_166_104_596_480
  | .cnot => 416_291_951_738_880
  | .singleQubit => 148_235_585

/-- One initial seed load, then 112 members with actual parallel reset and literal reload. -/
def quantumTimeBound : Nat := 117_480_458_204_112_193

/-- Paid source, packing, all recovery instructions, and the final seven-input selector. -/
def classicalOperationBound : Nat := 15_343_042_058_108_937_824

private lemma seedLabel_zero_or_power (width N : Nat) :
    (ShortDLP.CompiledMAU.Recycling.seedLabel width N).val = 0 ∨
      (ShortDLP.CompiledMAU.Recycling.seedLabel width N).val = 2 ^ width := by
  unfold ShortDLP.CompiledMAU.Recycling.seedLabel
    ShortDLP.CompiledMAU.Recycling.Arithmetic.encoding MAU.Exponentiation.Gidney.encoding
  simp only [BinaryLabelEncoding.prod_encode, BinaryLabelEncoding.finIdentity_encode,
    UnitaryCircuit.prodEquiv_value, Fin.val_zero, Nat.mul_zero, Nat.add_zero]
  unfold MAU.Multiplication.Accumulate.Gidney.encoding
  simp only [BinaryLabelEncoding.prod_encode, BinaryLabelEncoding.finIdentity_encode,
    UnitaryCircuit.prodEquiv_value]
  by_cases positive : 0 < N
  · by_cases fitted : N ≤ 2 ^ width
    · simp only [cleanWorkspace, dif_pos positive, dif_pos fitted, Fin.val_zero,
        Nat.zero_add, Nat.FixedWidth.unitResidueWord_one_val]
      have residue : 1 % N = 0 ∨ 1 % N = 1 := by
        have bounded := Nat.mod_le 1 N
        omega
      rcases residue with zero | one
      · simp only [zero, Nat.mul_zero, true_or]
      · simp only [one, Nat.mul_one]
        exact Or.inr rfl
    · simp [cleanWorkspace, positive, fitted, zeroWorkspace]
  · simp [cleanWorkspace, positive, zeroWorkspace]

/-- The new single-control bank's actual seed load uses at most one X, on every total branch. -/
lemma seedLoad_count_le_one (width N : Nat) :
    EncodedBit.Word.BasisLoad.xCount
      (ShortDLP.CompiledMAU.Recycling.seedLabel width N) ≤ 1 := by
  rw [EncodedBit.Word.BasisLoad.xCount, ← List.toFinset_card_of_nodup
    (EncodedBit.Word.constantOneIndices_nodup
      (ShortDLP.CompiledMAU.Recycling.seedLabel width N))]
  apply Finset.card_le_one.mpr
  intro left leftMember right rightMember
  have leftBit := (EncodedBit.Word.mem_constantOneIndices _ left).mp
    (List.mem_toFinset.mp leftMember)
  have rightBit := (EncodedBit.Word.mem_constantOneIndices _ right).mp
    (List.mem_toFinset.mp rightMember)
  rcases seedLabel_zero_or_power width N with zero | power
  · simp only [zero, Nat.zero_testBit, Bool.false_eq_true] at leftBit
  · rw [power, Nat.testBit_two_pow] at leftBit rightBit
    apply Fin.ext
    exact (of_decide_eq_true leftBit).symm.trans (of_decide_eq_true rightBit)

/-- Evaluate only the closed width formula, without expanding any real arithmetic circuit. -/
lemma selectedStageTimeBound_eq :
    MAU.Multiplication.Gidney.controlledTimeBound 2_048 = selectedStageTimeBound :=
  MAU.Multiplication.Gidney.controlledBounds_2048.2.2

/-- Both controlled MACs contribute their real bi-flip CNOT allowances. -/
lemma selectedStageCnotBound_eq :
    MAU.Multiplication.Gidney.controlledCnotBound 2_048 = selectedStageCnotBound :=
  MAU.Multiplication.Gidney.controlledBounds_2048.1

/-- Both controlled MACs and the selected word swap contribute their Toffoli allowances. -/
lemma selectedStageToffoliBound_eq :
    MAU.Multiplication.Gidney.controlledToffoliBound 2_048 = selectedStageToffoliBound :=
  MAU.Multiplication.Gidney.controlledBounds_2048.2.1

/-- The actual one-control arithmetic uses the newly pushed-control selected stage. -/
lemma actualArithmetic_native_counts (modulus : Fin (2 ^ 2_048 + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.program
        (width := 2_048) modulus coefficient).eventCost = 0 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (ShortDLP.CompiledMAU.Recycling.Arithmetic.program
        (width := 2_048) modulus coefficient).eventCost ≤
        selectedStageCnotBound := by
  have actual := MAU.Multiplication.Gidney.gidneyControlledUnitMultiplication_native_counts
    1 2_048 (0 : Fin 1) modulus
    (Nat.FixedWidth.UnitExponentiation.stageUnit coefficient (0 : Fin 1))
  exact ⟨actual.1, actual.2.trans_eq selectedStageCnotBound_eq⟩

/-- Both measured exponent streams retain their own previous-bit feedback sum. -/
lemma feedbackPhaseBound_eq :
    (513 + 1_025).choose 2 + (513 : Nat).choose 2 = feedbackPhaseBound := by
  norm_num [feedbackPhaseBound, Nat.choose_two_right]

/-- The actual member's independent quantum-time formula has this fixed numerical ceiling. -/
lemma measuredMemberTimeBound_eq :
    ShortDLP.CompiledMAU.Recycling.Resources.memberTime 1_025 513 2_048 =
      measuredMemberTimeBound := by
  rw [ShortDLP.CompiledMAU.Recycling.Resources.memberTime, selectedStageTimeBound_eq,
    feedbackPhaseBound_eq]
  norm_num [ShortDLP.CompiledMAU.Recycling.resultBits,
    selectedStageTimeBound, feedbackPhaseBound, measuredMemberTimeBound]

private lemma round_gate_count (m ell width N : Nat) (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate coordinate)
      (RSA.Recycling.Program.roundEventBudget m ell width N) =
        ShortDLP.CompiledMAU.Recycling.resultBits m ell *
          ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound width coordinate +
        if coordinate = .singleQubit then
          3 * ShortDLP.CompiledMAU.Recycling.resultBits m ell +
            (ell + m).choose 2 + ell.choose 2 + (1 + 2 * width) +
            EncodedBit.Word.BasisLoad.xCount
              (ShortDLP.CompiledMAU.Recycling.seedLabel width N)
        else 0 := by
  cases coordinate
  all_goals
    simp [RSA.Recycling.Program.roundEventBudget, RSA.Recycling.Program.packingEventBudget,
      RSA.Recycling.Program.seedEventBudget, ShortDLP.CompiledMAU.Recycling.BankReset.eventBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.memberBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.baseBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.arithmeticBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
      ShortDLP.CompiledMAU.Recycling.Resources.oneQubit,
      ShortDLP.CompiledMAU.Recycling.Resources.oneMeasurement]
  all_goals ring

private lemma seven_gate_count (N : Nat) (coordinate : AlgorithmGate.Coordinate) :
    RSA.Recycling.Program.gateCountLimit N 7 coordinate =
      112 * ResourcePool.count (model := Model) (.gate coordinate)
        (RSA.Recycling.Program.roundEventBudget
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) +
      if coordinate = .singleQubit then
        EncodedBit.Word.BasisLoad.xCount
          (ShortDLP.CompiledMAU.Recycling.seedLabel (arithmeticBits N) N)
      else 0 := by
  have sourceZero := RecoveryNativeGates.sampler_gate_zero (model := Model) coordinate N
  have recoveryZero := RecoveryNativeGates.recovery_gate_zero (model := Model) coordinate N
  have selectionZero := RecoveryNativeGates.optional_gate_zero
    (model := Model) coordinate (modulusBits N) 7
  simp only [RSA.Recycling.Program.gateCountLimit, RSA.Recycling.Program.eventBudget,
    RSA.Recycling.Program.batchEventBudget, RSA.Recycling.Program.bodyEventBudget,
    RSA.Recycling.Program.sourceEventBudget, RSA.Recycling.Program.recoveryEventBudget,
    RSA.Recycling.Program.selectionEventBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, sourceZero, recoveryZero, selectionZero, zero_add, add_zero]
  cases coordinate <;>
    simp [RSA.Recycling.Program.preparationEventBudget, RSA.Recycling.Program.seedEventBudget]
    <;> ring

/-- Every original exact-width key has all three independent native gate ceilings. -/
lemma model_gateCountLimit_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (coordinate : AlgorithmGate.Coordinate) :
    RSA.Recycling.Program.gateCountLimit N NativeRSA2048.rounds coordinate ≤
      gateCountBound coordinate := by
  have load := seedLoad_count_le_one 2_048 N
  have arithmetic := NativeRSA2048.model_arithmeticBits_eq model
  norm_num only [NativeRSA2048.modulusBits, NativeRSA2048.primeBits] at arithmetic
  rw [NativeRSA2048.rounds, seven_gate_count, round_gate_count,
    NativeRSA2048.model_shortLogBits_eq model, NativeRSA2048.model_tradeoffBits_eq model,
    arithmetic]
  cases coordinate with
  | toffoli =>
      have different : AlgorithmGate.Coordinate.toffoli ≠
          AlgorithmGate.Coordinate.singleQubit := by
        intro same
        cases same
      norm_num [gateCountBound, ShortDLP.CompiledMAU.Recycling.resultBits,
        ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
        selectedStageToffoliBound_eq, selectedStageToffoliBound, Nat.choose_two_right, different]
  | cnot =>
      have different : AlgorithmGate.Coordinate.cnot ≠
          AlgorithmGate.Coordinate.singleQubit := by
        intro same
        cases same
      norm_num [gateCountBound, ShortDLP.CompiledMAU.Recycling.resultBits,
        ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
        selectedStageCnotBound_eq, selectedStageCnotBound, Nat.choose_two_right, different]
  | singleQubit =>
      norm_num [gateCountBound, ShortDLP.CompiledMAU.Recycling.resultBits,
        ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound, Nat.choose_two_right]
      omega

/-- The same seven-batch run has the complete parameter-only quantum-time ceiling. -/
lemma model_quantumTimeLimit_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Recycling.Program.quantumTimeLimit N NativeRSA2048.rounds ≤ quantumTimeBound := by
  have load := seedLoad_count_le_one (arithmeticBits N) N
  have arithmetic := NativeRSA2048.model_arithmeticBits_eq model
  norm_num only [NativeRSA2048.modulusBits, NativeRSA2048.primeBits] at arithmetic
  change RSA.Recycling.Program.seedLoadQuantumTime N +
    112 * (ShortDLP.CompiledMAU.Recycling.Resources.memberTime
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) + 1 +
        RSA.Recycling.Program.seedLoadQuantumTime N) ≤ quantumTimeBound
  rw [NativeRSA2048.model_shortLogBits_eq model,
    NativeRSA2048.model_tradeoffBits_eq model, arithmetic, measuredMemberTimeBound_eq]
  change RSA.Recycling.Program.seedLoadQuantumTime N ≤ 1 at load
  norm_num [measuredMemberTimeBound, quantumTimeBound] at *
  omega

private lemma classicalWeight_le_card (pool : ResourcePool Model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bound := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event Model => 1) (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bound

private lemma round_classicalWeight (m ell width N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (RSA.Recycling.Program.roundEventBudget m ell width N) = 1 := by
  simp [RSA.Recycling.Program.roundEventBudget, RSA.Recycling.Program.packingEventBudget,
    RSA.Recycling.Program.seedEventBudget, ShortDLP.CompiledMAU.Recycling.BankReset.eventBudget,
    ShortDLP.CompiledMAU.Recycling.Resources.memberBudget,
    ShortDLP.CompiledMAU.Recycling.Resources.baseBudget,
    ShortDLP.CompiledMAU.Recycling.Resources.arithmeticBudget,
    ShortDLP.CompiledMAU.Recycling.Resources.oneQubit,
    ShortDLP.CompiledMAU.Recycling.Resources.oneMeasurement,
    Resource.Event.classicalOperationWeight]

private lemma seven_classicalWeight (N : Nat) :
    RSA.Recycling.Program.classicalOperationLimit N 7 ≤
      7 * (44 * modulusBits N + 182 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 1 := by
  have sourceBound := (classicalWeight_le_card
    (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N)).trans_eq
      (ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card Model N)
  have recoveryBound := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
    (model := Model) N
  unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width at recoveryBound
  have selectionBound := (classicalWeight_le_card
    (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) 7)).trans_eq
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope_card Model (modulusBits N) 7)
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N) ≤
        44 * modulusBits N + 163 at sourceBound
  change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) 7) ≤
        22 at selectionBound
  simp only [RSA.Recycling.Program.classicalOperationLimit, RSA.Recycling.Program.eventBudget,
    RSA.Recycling.Program.batchEventBudget, RSA.Recycling.Program.bodyEventBudget,
    RSA.Recycling.Program.sourceEventBudget, RSA.Recycling.Program.recoveryEventBudget,
    RSA.Recycling.Program.selectionEventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, round_classicalWeight]
  simp only [RSA.Recycling.Program.preparationEventBudget, RSA.Recycling.Program.seedEventBudget,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.classicalOperationWeight, mul_zero, zero_add]
  change 7 * (ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N) +
        (16 + ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := Model) N))) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N) 7) ≤
      7 * (44 * modulusBits N + 182 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 1
  calc
    _ ≤ 7 * ((44 * modulusBits N + 163) +
        (16 + LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)))) + 22 :=
      Nat.add_le_add (Nat.mul_le_mul_left 7
        (Nat.add_le_add sourceBound (Nat.add_le_add_left recoveryBound 16))) selectionBound
    _ = _ := by ring

/-- The full classical-only ceiling evaluates the unchanged recovery width formula. -/
lemma model_classicalOperationLimit_le {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) :
    RSA.Recycling.Program.classicalOperationLimit N NativeRSA2048.rounds ≤
      classicalOperationBound := by
  refine (seven_classicalWeight N).trans_eq ?_
  rw [NativeRSA2048.model_coordinateWidth_eq model,
    NativeRSA2048.model_modulusBits_eq model, NativeRSA2048.model_shortLogBits_eq model,
    NativeRSA2048.model_tradeoffBits_eq model]
  change 7 * (44 * 2_048 + 182 + LatticeFixedBatchRecoveryMachine.eventCountBound
    2_048 1_025 513 7_522_484_226) + 1 = classicalOperationBound
  rw [NativeRSA2048.recoveryEventCountWidthBound_eq]
  norm_num [NativeRSA2048.recoveryEventCountBound, classicalOperationBound]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- All three native gate bounds apply to each path of the actual seven-batch execution. -/
lemma run_gateCount_le (model : NativeRSA2048.FixedWidthModel N) (input : Input N)
    (path : (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate coordinate)
      ((RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.resourcePool
        path) ≤ gateCountBound coordinate :=
  (RSA.Recycling.Program.rsaRecyclingParent_run_gateCount_le
    base noQuantum input NativeRSA2048.rounds path coordinate).trans
      (model_gateCountLimit_le model coordinate)

/-- Quantum time belongs to the same literal path as the complete state and success contracts. -/
lemma run_quantumTime_le (model : NativeRSA2048.FixedWidthModel N) (input : Input N)
    (path : (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.Path) :
    (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.quantumTime path ≤
      quantumTimeBound :=
  (RSA.Recycling.Program.rsaRecyclingParent_run_quantumTime_le
    base noQuantum N input NativeRSA2048.rounds path).trans (model_quantumTimeLimit_le model)

/-- The paid classical ceiling includes every actual source, pack, recovery and selector step. -/
lemma run_classicalOperation_le (model : NativeRSA2048.FixedWidthModel N) (input : Input N)
    (path : (RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((RSA.Recycling.Program.run base noQuantum N input NativeRSA2048.rounds).code.resourcePool
        path) ≤ classicalOperationBound :=
  (RSA.Recycling.Program.rsaRecyclingParent_run_classicalOperation_le
    base noQuantum input NativeRSA2048.rounds path).trans (model_classicalOperationLimit_le model)

end

end QuantumAlg.Factoring.RSA2048.Recycling
