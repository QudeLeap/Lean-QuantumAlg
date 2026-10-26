/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight

import all QuantumAlg.Algorithms.Factoring.RSA
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.QuantumTime
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Gates
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Space
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Context
import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import all QuantumAlg.Util.RSA.ShortLog.Widths.SameBit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Bounds
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Resources.Pool

/-!
# Closed scalar bounds for the actual single-control RSA execution

These identities and inequalities expand the independently specified event,
space and whole-run quantum-time allowances. They never inspect a run's event
list or execution AST. The conversion from the recovery operand width to the
public modulus width uses an actual same-bit RSA key, since natural-number
size and ceiling binary logarithm need not agree on arbitrary natural numbers.

The same-bit resource bounds apply to every key in the original carrier;
they do not require the exceptional-key success premise. The final theorems
also observe the existing independently defined public factoring problem.
-/

namespace QuantumAlg.Factoring.RSA

noncomputable section

variable [configuration : Configuration]

/-- Independent quantum-system allowance for one reusable bank, or zero for zero batches. -/
public def qubitBoundAtCount (N count : Nat) : Nat :=
  Measured.Program.qubitLimit N count

/-- Independent classical allowance for the retained frame and simultaneous temporary storage. -/
public def classicalBitBoundAtCount (N count : Nat) : Nat :=
  Measured.Program.classicalBitLimit N count

/-- Tight original key-domain native allowance at any count and gate coordinate. -/
public def gateCountBoundAtCount (N count : Nat)
    (coordinate : AlgorithmGate.Coordinate) : Nat :=
  Measured.Program.gateCountLimit N count coordinate

/-- Tight original key-domain weighted-work time ceiling, zero for zero batches. -/
public def quantumTimeBoundAtCount (N count : Nat) : Nat :=
  Measured.Program.quantumTimeLimit N count

/-- Symbolic ceiling for literal classical operations on the actual path. -/
public def classicalOperationBoundAtCount (N count : Nat) : Nat :=
  Measured.Program.classicalOperationLimit N count

end

end QuantumAlg.Factoring.RSA

namespace QuantumAlg.Factoring.RSA.ScalarBounds

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines ClassicalRoutines.NumberTheory
open EkeraHastadStyle.Canonical LatticeRecoveryResources

local instance {A : Type} : DecidableEq A := Classical.decEq A

private abbrev Model := ShortDLP.CompiledMAU.Recycling.model

/-- Allocated coordinate width used by deterministic lattice recovery. -/
public def coordinateEnvelope (N : Nat) : Nat :=
  2 ^ 21 * (modulusBits N + tradeoffBits N + shortLogBits N + 1) + 2


/-- Scalar workspace envelope for the deterministic lattice recovery stage. -/
public def recoverySpaceEnvelope (N : Nat) : Nat :=
  140 * coordinateEnvelope N + 6 * modulusBits N + 6 * measurementBits N + 91


/-- Scalar event envelope for the deterministic lattice recovery stage. -/
public def recoveryEventEnvelope (N : Nat) : Nat :=
  LatticeFixedBatchRecoveryMachine.eventCountBound
    (modulusBits N) (shortLogBits N) (tradeoffBits N)
    (coordinateEnvelope N) configuration.additionalMembers


/-- Scalar envelope for chronological feedback rotations across both measured exponent registers. -/
public def feedbackEnvelope (N : Nat) : Nat :=
  (shortLogBits N + tradeoffBits N).choose 2 + (tradeoffBits N).choose 2


/-- Quantum-system envelope for one control qubit and two arithmetic words. -/
public def qubitEnvelope (N : Nat) : Nat := 2 * arithmeticBits N + 4


/-- Both controlled MACs and the selected swap use the canonical Toffoli allowance. -/
public def toffoliEnvelope (N count : Nat) : Nat :=
  membersPerBatch * count * measurementBits N *
    (28 * arithmeticBits N ^ 2 - 45 * arithmeticBits N)

/-- Both controlled MACs use the canonical CNOT allowance. -/
public def cnotEnvelope (N count : Nat) : Nat :=
  membersPerBatch * count * measurementBits N *
    (108 * arithmeticBits N ^ 2 - 178 * arithmeticBits N)

/-- Paid arithmetic H/reset/Z, loading, feedback and complete reset have their own coordinate. -/
public def singleQubitEnvelope (N count : Nat) : Nat :=
  1 + membersPerBatch * count *
    (measurementBits N * (24 * arithmeticBits N ^ 2 - 32 * arithmeticBits N + 3) +
      feedbackEnvelope N + qubitEnvelope N + 1)

/-- Weighted native quantum work bounds the actual schedule without a depth-optimality claim. -/
public def quantumTimeEnvelope (N count : Nat) : Nat :=
  toffoliEnvelope N count + cnotEnvelope N count + singleQubitEnvelope N count


/-- Whole-run scalar envelope for literal classical operations and deterministic recovery. -/
public def classicalOperationEnvelope (N count : Nat) : Nat :=
  count * (44 * modulusBits N + 166 + membersPerBatch + recoveryEventEnvelope N) + 1


/-- Whole-run scalar envelope for stored batch data and reusable classical workspace. -/
public def classicalSpaceEnvelope (N count : Nat) : Nat :=
  count * (19 * modulusBits N + membersPerBatch * measurementBits N + 2) + modulusBits N + 1 +
    (measurementBits N + (arithmeticBits N - 2)) + max (9 * modulusBits N + 14)
      (max (recoverySpaceEnvelope N + 8 * modulusBits N + 2)
        (max (qubitEnvelope N) (2 * modulusBits N + 2)))

omit configuration in
/-- The recovery coordinate's size/log conversion is restricted to the original key carrier. -/
lemma sameBit_size_eq_clog {bitWidth : Nat} (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth)
    (positive : 1 ≤ bitWidth) :
    Nat.size pair.modulus = Nat.clog 2 pair.modulus :=
  (QuantumAlg.RSA.FixedWidthSampling.modulus_size_eq_two_mul pair positive).trans
    (QuantumAlg.RSA.FixedWidthSampling.modulus_clog_eq_two_mul pair positive).symm

omit configuration in
/-- The public coordinate formula equals the existing recovery width on every same-bit key. -/
lemma sameBit_coordinateEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth) :
    QuantumAlg.RSA.ShortLogWidths.coordinateWidth pair.modulus
      (shortLogBits pair.modulus) (tradeoffBits pair.modulus) =
        coordinateEnvelope pair.modulus := by
  unfold QuantumAlg.RSA.ShortLogWidths.coordinateWidth
    QuantumAlg.RSA.ShortLogWidths.operandWidthBound
    QuantumAlg.RSA.ShortLogWidths.inputBitWidth QuantumAlg.RSA.shortLogRecoveryInputBits
  rw [sameBit_size_eq_clog pair positive]
  change 2 * (2 ^ 20 * (modulusBits pair.modulus + tradeoffBits pair.modulus +
    shortLogBits pair.modulus + 1)) + 2 = coordinateEnvelope pair.modulus
  unfold coordinateEnvelope
  norm_num
  ring

omit configuration in
private lemma pairAllocation_eq (N : Nat) :
    LatticePairRecoveryWorkspace.allocationBits N =
      104 * LatticeWideLllMachine.Width N + 5 * modulusBits N +
        6 * measurementBits N + 33 := by
  have combined := BatchMachine.measurementBits_eq_jkWidth N
  unfold LatticePairRecoveryWorkspace.allocationBits
  omega

omit configuration in
private lemma quadraticAllocation_polynomial (width : Nat) :
    5 * QuadraticPrefix.discriminantWidth width +
      7 * QuadraticCandidateCheck.CandidateWidth width + QuadraticPrefix.centerWidth width +
      8 * NatSqrt.workWidth (QuadraticPrefix.discriminantWidth width) + 10 =
        34 * width + 51 := by
  simp only [QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth,
    QuadraticCandidateCheck.CandidateWidth, NatSqrt.workWidth]
  omega

omit configuration in
private lemma quadraticAllocation_eq (N : Nat) :
    QuadraticScratchLayout.allocationBits N =
      34 * LatticePairCandidateRecovery.Width N + 51 := by
  exact quadraticAllocation_polynomial (LatticePairCandidateRecovery.Width N)

omit configuration in
/-- Exact allocation of the actual simultaneous recovery packages on every natural modulus. -/
lemma recoveryAllocation_eq (N : Nat) :
    LatticeBatchRecoveryWorkspace.allocationBits N =
      140 * QuantumAlg.RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N) +
        6 * modulusBits N + 6 * measurementBits N + 91 := by
  rw [LatticeBatchRecoveryWorkspace.allocationBits, pairAllocation_eq, quadraticAllocation_eq]
  change 2 * (LatticePairCandidateRecovery.Width N + 1 + 1) + modulusBits N + 3 +
    (104 * LatticeWideLllMachine.Width N + 5 * modulusBits N + 6 * measurementBits N + 33) +
    (34 * LatticePairCandidateRecovery.Width N + 51) = _
  unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width
  ring

omit configuration in
/-- The public recovery-space expression equals the actual allocation on original same-bit keys. -/
lemma sameBit_recoverySpaceEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth) :
    LatticeBatchRecoveryWorkspace.allocationBits pair.modulus =
      recoverySpaceEnvelope pair.modulus := by
  rw [recoveryAllocation_eq, sameBit_coordinateEnvelope_eq pair positive]; rfl

/-- The displayed recovery-event ceiling is the same parameter bound on each original key. -/
lemma sameBit_recoveryEventEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth) :
    LatticeFixedBatchRecoveryMachine.eventCountBound (modulusBits pair.modulus)
      (shortLogBits pair.modulus) (tradeoffBits pair.modulus)
      (LatticePairCandidateRecovery.Width pair.modulus) configuration.additionalMembers =
        recoveryEventEnvelope pair.modulus := by
  unfold recoveryEventEnvelope LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width
  rw [sameBit_coordinateEnvelope_eq pair positive]

omit configuration in
/-- The literal actual measured seed loader has at most one X on every total parameter branch. -/
lemma rsaScalar_seedLoad_count_le_one (width N : Nat) :
    EncodedBit.Word.BasisLoad.xCount
      (ShortDLP.CompiledMAU.Recycling.Measured.seedLabel width N) ≤ 1 :=
  ShortDLP.CompiledMAU.Recycling.Measured.measuredSeed_xCount_le_one width N

private def arithmeticGateBound (width : Nat) : AlgorithmGate.Coordinate → Nat
  | .toffoli => 28 * width ^ 2 - 45 * width
  | .cnot => 108 * width ^ 2 - 178 * width
  | .singleQubit => 24 * width ^ 2 - 32 * width

omit configuration in
private lemma round_gate_count (m ell width N : Nat)
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


/-- Complete positive-count gate limits count only the actual independent quantum-gate pool. -/
lemma positive_gateCountLimit_eq (N laterCount : Nat) (coordinate : AlgorithmGate.Coordinate) :
    RSA.Measured.Program.gateCountLimit N (laterCount + 1) coordinate =
      membersPerBatch * (laterCount + 1) * ResourcePool.count (model := Model) (.gate coordinate)
        (RSA.Measured.Program.roundEventBudget
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) +
      if coordinate = .singleQubit then
        EncodedBit.Word.BasisLoad.xCount
          (ShortDLP.CompiledMAU.Recycling.Measured.seedLabel (arithmeticBits N) N)
      else 0 := by
  have sourceZero := RecoveryNativeGates.sampler_gate_zero (model := Model) coordinate N
  have recoveryZero := RecoveryNativeGates.recovery_gate_zero (model := Model) coordinate N
    configuration.additionalMembers
  have selectionZero := RecoveryNativeGates.optional_gate_zero
    (model := Model) coordinate (modulusBits N) (laterCount + 1)
  simp only [RSA.Measured.Program.gateCountLimit, RSA.Measured.Program.eventBudget,
    RSA.Measured.Program.batchEventBudget, RSA.Measured.Program.bodyEventBudget,
    RSA.Measured.Program.sourceEventBudget, RSA.Measured.Program.recoveryEventBudget,
    RSA.Measured.Program.selectionEventBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, sourceZero, recoveryZero, selectionZero, zero_add, add_zero]
  cases coordinate <;>
    (simp [RSA.Measured.Program.preparationEventBudget, RSA.Measured.Program.seedEventBudget];
      ring)

omit configuration in
private lemma resultBits_parameters (N : Nat) :
    ShortDLP.CompiledMAU.Recycling.resultBits (shortLogBits N) (tradeoffBits N) =
      measurementBits N := rfl

/-- The independent positive-count pool has exactly its canonical Toffoli allowance. -/
public lemma toffoliEnvelope_eq (N laterCount : Nat) :
    RSA.gateCountBoundAtCount N (laterCount + 1) .toffoli =
      toffoliEnvelope N (laterCount + 1) := by
  change RSA.Measured.Program.gateCountLimit N (laterCount + 1) .toffoli = _
  rw [positive_gateCountLimit_eq, round_gate_count]
  simp only [arithmeticGateBound,
    if_neg (show AlgorithmGate.Coordinate.toffoli ≠ .singleQubit by decide),
    Nat.add_zero, resultBits_parameters]
  unfold toffoliEnvelope
  ring

/-- The independent positive-count pool has exactly its canonical CNOT allowance. -/
public lemma cnotEnvelope_eq (N laterCount : Nat) :
    RSA.gateCountBoundAtCount N (laterCount + 1) .cnot =
      cnotEnvelope N (laterCount + 1) := by
  change RSA.Measured.Program.gateCountLimit N (laterCount + 1) .cnot = _
  rw [positive_gateCountLimit_eq, round_gate_count]
  simp only [arithmeticGateBound,
    if_neg (show AlgorithmGate.Coordinate.cnot ≠ .singleQubit by decide),
    Nat.add_zero, resultBits_parameters]
  unfold cnotEnvelope
  ring

/-- The independent single-qubit ceiling pays all measured arithmetic and peripheral gates. -/
public lemma singleQubitEnvelope_le (N laterCount : Nat) :
    RSA.gateCountBoundAtCount N (laterCount + 1) .singleQubit ≤
      singleQubitEnvelope N (laterCount + 1) := by
  have load := rsaScalar_seedLoad_count_le_one (arithmeticBits N) N
  change RSA.Measured.Program.gateCountLimit N (laterCount + 1) .singleQubit ≤ _
  rw [positive_gateCountLimit_eq, round_gate_count]
  simp only [arithmeticGateBound, resultBits_parameters]
  have roundBound :
      measurementBits N * (24 * arithmeticBits N ^ 2 - 32 * arithmeticBits N) +
        (3 * measurementBits N + (tradeoffBits N + shortLogBits N).choose 2 +
          (tradeoffBits N).choose 2 + (2 * arithmeticBits N + 4) +
          EncodedBit.Word.BasisLoad.xCount
            (ShortDLP.CompiledMAU.Recycling.Measured.seedLabel (arithmeticBits N) N)) ≤
      measurementBits N * (24 * arithmeticBits N ^ 2 - 32 * arithmeticBits N + 3) +
        feedbackEnvelope N + qubitEnvelope N + 1 := by
    unfold feedbackEnvelope qubitEnvelope
    rw [Nat.add_comm (shortLogBits N) (tradeoffBits N), Nat.mul_add]
    omega
  exact (Nat.add_le_add
    (Nat.mul_le_mul_left (membersPerBatch * (laterCount + 1)) roundBound) load).trans_eq
      (by unfold singleQubitEnvelope; ring)

omit configuration in
private lemma quantumWork_gateCounts (pool : ResourcePool Model) :
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

/-- The actual-schedule allowance is bounded by the separate sum of native quantum coordinates. -/
public lemma quantumTimeEnvelope_le (N laterCount : Nat) :
    RSA.quantumTimeBoundAtCount N (laterCount + 1) ≤
      quantumTimeEnvelope N (laterCount + 1) := by
  change ResourcePool.weightedCount Resource.Event.quantumDuration
    (RSA.Measured.Program.eventBudget N (laterCount + 1)) ≤ _
  rw [quantumWork_gateCounts]
  change RSA.gateCountBoundAtCount N (laterCount + 1) .toffoli +
    RSA.gateCountBoundAtCount N (laterCount + 1) .cnot +
    RSA.gateCountBoundAtCount N (laterCount + 1) .singleQubit ≤ _
  rw [toffoliEnvelope_eq, cnotEnvelope_eq]
  exact Nat.add_le_add_left (singleQubitEnvelope_le N laterCount)
    (toffoliEnvelope N (laterCount + 1) + cnotEnvelope N (laterCount + 1))

omit configuration in
private lemma classicalWeight_le_card (pool : ResourcePool Model) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool ≤ pool.card := by
  have bound := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event Model => 1) (s := pool)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one] using bound

omit configuration in
private lemma round_classicalWeight (m ell width N : Nat) :
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

private lemma positive_classicalOperationLimit_le (N laterCount : Nat) :
    RSA.Measured.Program.classicalOperationLimit N (laterCount + 1) ≤
      (laterCount + 1) * (44 * modulusBits N + 166 + membersPerBatch +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (LatticePairCandidateRecovery.Width N) configuration.additionalMembers) + 1 := by
  have sourceBound := (classicalWeight_le_card
    (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N)).trans_eq
      (ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card Model N)
  have recoveryBound := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
    (model := Model) N configuration.additionalMembers
  have selectionBound := (classicalWeight_le_card
    (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N)
      (laterCount + 1))).trans_eq
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope_card
        Model (modulusBits N) (laterCount + 1))
  simp only [RSA.Measured.Program.classicalOperationLimit, RSA.Measured.Program.eventBudget,
    RSA.Measured.Program.batchEventBudget, RSA.Measured.Program.bodyEventBudget,
    RSA.Measured.Program.sourceEventBudget, RSA.Measured.Program.recoveryEventBudget,
    RSA.Measured.Program.selectionEventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, round_classicalWeight]
  simp only [RSA.Measured.Program.preparationEventBudget, RSA.Measured.Program.seedEventBudget,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.classicalOperationWeight, mul_zero, zero_add, Nat.mul_one]
  exact (Nat.add_le_add
    (Nat.mul_le_mul_left (laterCount + 1)
      (Nat.add_le_add sourceBound (Nat.add_le_add_left recoveryBound membersPerBatch)))
    selectionBound).trans_eq (by simp only [modulusBits]; ring)

/-- Every original same-bit key has the displayed paid classical-operation ceiling. -/
private lemma sameBit_classicalOperationEnvelope_le_proof {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth)
    (laterCount : Nat) :
    RSA.Measured.Program.classicalOperationLimit pair.modulus (laterCount + 1) ≤
      classicalOperationEnvelope pair.modulus (laterCount + 1) := by
  refine (positive_classicalOperationLimit_le pair.modulus laterCount).trans_eq ?_
  rw [sameBit_recoveryEventEnvelope_eq pair positive]; rfl

public lemma sameBit_classicalOperationEnvelope_le {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth)
    (laterCount : Nat) :
    RSA.classicalOperationBoundAtCount pair.modulus (laterCount + 1) ≤
      classicalOperationEnvelope pair.modulus (laterCount + 1) :=
  sameBit_classicalOperationEnvelope_le_proof pair positive laterCount

private lemma sameBit_classicalSpaceEnvelope_eq_proof {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth)
    (laterCount : Nat) :
    RSA.Measured.Program.classicalBitLimit pair.modulus (laterCount + 1) =
      classicalSpaceEnvelope pair.modulus (laterCount + 1) := by
  rw [RSA.Measured.Program.classicalBitLimit, RSA.Recycling.ClassicalFrame.classicalBits,
    sameBit_recoverySpaceEnvelope_eq pair positive]; rfl

public lemma sameBit_classicalSpaceEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth)
    (laterCount : Nat) :
    RSA.classicalBitBoundAtCount pair.modulus (laterCount + 1) =
      classicalSpaceEnvelope pair.modulus (laterCount + 1) :=
  sameBit_classicalSpaceEnvelope_eq_proof pair positive laterCount

private lemma sameBit_positive_scalar_bounds_proof (N laterCount : Nat)
    (key : GoodKeyModel N) :
    RSA.Measured.Program.spaceLimit N (laterCount + 1) .classicalBits =
        classicalSpaceEnvelope N (laterCount + 1) ∧
    RSA.Measured.Program.spaceLimit N (laterCount + 1) (.quantumSystems 2) =
        qubitEnvelope N ∧
    RSA.Measured.Program.gateCountLimit N (laterCount + 1) .toffoli =
        toffoliEnvelope N (laterCount + 1) ∧
    RSA.Measured.Program.gateCountLimit N (laterCount + 1) .cnot =
        cnotEnvelope N (laterCount + 1) ∧
    RSA.Measured.Program.gateCountLimit N (laterCount + 1) .singleQubit ≤
        singleQubitEnvelope N (laterCount + 1) ∧
    RSA.Measured.Program.quantumTimeLimit N (laterCount + 1) ≤
        quantumTimeEnvelope N (laterCount + 1) ∧
    RSA.Measured.Program.classicalOperationLimit N (laterCount + 1) ≤
        classicalOperationEnvelope N (laterCount + 1) := by
  rcases key with ⟨bitWidth, pair, rfl, effectiveRange, _⟩
  have effective : 512 ≤ bitWidth := effectiveRange
  have positive : 1 ≤ bitWidth := by omega
  have classical := sameBit_classicalSpaceEnvelope_eq_proof pair positive laterCount
  have classicalOps := sameBit_classicalOperationEnvelope_le_proof pair positive laterCount
  have qubits :
      RSA.Measured.Program.spaceLimit pair.modulus (laterCount + 1) (.quantumSystems 2) =
        qubitEnvelope pair.modulus := by
    simpa only [RSA.Measured.Program.qubitLimit, qubitEnvelope] using
      RSA.Measured.Program.rsaMeasuredParent_spaceLimit_qubits pair.modulus (laterCount + 1)
  have classicalSpace :=
    (RSA.Measured.Program.rsaMeasuredParent_spaceLimit_classicalBits pair.modulus
      (laterCount + 1)).trans classical
  have toffoli := toffoliEnvelope_eq pair.modulus laterCount
  have cnot := cnotEnvelope_eq pair.modulus laterCount
  have singleQubit := singleQubitEnvelope_le pair.modulus laterCount
  have quantumTime := quantumTimeEnvelope_le pair.modulus laterCount
  have bounds := And.intro classicalSpace
    (And.intro qubits (And.intro toffoli (And.intro cnot
      (And.intro singleQubit (And.intro quantumTime classicalOps)))))
  exact bounds


public lemma problem_scalar_bounds (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat} (key : GoodKeyModel N)
    (η : Real) (etaPositive : 0 < η) (etaLessOne : η < 1) :
    let count := NativeFiniteRetry.Calibration.retryCount η
    (RSA.problem base noQuantum N η).resources.resident .classicalBits =
        base.residentSpace .classicalBits + classicalSpaceEnvelope N count ∧
    (RSA.problem base noQuantum N η).resources.auxiliary .classicalBits =
        base.auxiliarySpace .classicalBits + classicalSpaceEnvelope N count ∧
    (RSA.problem base noQuantum N η).resources.resident (.quantumSystems 2) =
        base.residentSpace (.quantumSystems 2) + qubitEnvelope N ∧
    (RSA.problem base noQuantum N η).resources.auxiliary (.quantumSystems 2) =
        base.auxiliarySpace (.quantumSystems 2) + qubitEnvelope N ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .toffoli)
        (RSA.problem base noQuantum N η).resources.events = toffoliEnvelope N count ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .cnot)
        (RSA.problem base noQuantum N η).resources.events = cnotEnvelope N count ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (.gate .singleQubit)
        (RSA.problem base noQuantum N η).resources.events ≤ singleQubitEnvelope N count ∧
    (RSA.problem base noQuantum N η).quantumTimeLimit ≤ quantumTimeEnvelope N count ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (RSA.problem base noQuantum N η).resources.events ≤
          classicalOperationEnvelope N count := by
  let count := NativeFiniteRetry.Calibration.retryCount η
  have countPositive : 0 < count :=
    NativeFiniteRetry.Calibration.realRetryCount_pos η etaPositive etaLessOne
  obtain ⟨laterCount, countEq⟩ : ∃ laterCount, count = laterCount + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt countPositive)
  obtain ⟨classicalSpace, qubits, toffoli, cnot, singleQubit, quantumTime, classicalOps⟩ :=
    sameBit_positive_scalar_bounds_proof N laterCount key
  change
    base.residentSpace .classicalBits +
        RSA.Measured.Program.spaceLimit N count .classicalBits =
        base.residentSpace .classicalBits + classicalSpaceEnvelope N count ∧
    base.auxiliarySpace .classicalBits +
        RSA.Measured.Program.spaceLimit N count .classicalBits =
        base.auxiliarySpace .classicalBits + classicalSpaceEnvelope N count ∧
    base.residentSpace (.quantumSystems 2) +
        RSA.Measured.Program.spaceLimit N count (.quantumSystems 2) =
        base.residentSpace (.quantumSystems 2) + qubitEnvelope N ∧
    base.auxiliarySpace (.quantumSystems 2) +
        RSA.Measured.Program.spaceLimit N count (.quantumSystems 2) =
        base.auxiliarySpace (.quantumSystems 2) + qubitEnvelope N ∧
    RSA.Measured.Program.gateCountLimit N count .toffoli = toffoliEnvelope N count ∧
    RSA.Measured.Program.gateCountLimit N count .cnot = cnotEnvelope N count ∧
    RSA.Measured.Program.gateCountLimit N count .singleQubit ≤ singleQubitEnvelope N count ∧
    RSA.Measured.Program.quantumTimeLimit N count ≤ quantumTimeEnvelope N count ∧
    RSA.Measured.Program.classicalOperationLimit N count ≤ classicalOperationEnvelope N count
  simp only [countEq]
  exact ⟨congrArg (fun bits : Nat => base.residentSpace .classicalBits + bits) classicalSpace,
    congrArg (fun bits : Nat => base.auxiliarySpace .classicalBits + bits) classicalSpace,
    congrArg (fun bits : Nat => base.residentSpace (.quantumSystems 2) + bits) qubits,
    congrArg (fun bits : Nat => base.auxiliarySpace (.quantumSystems 2) + bits) qubits,
    toffoli, cnot, singleQubit, quantumTime, classicalOps⟩

end

end QuantumAlg.Factoring.RSA.ScalarBounds
