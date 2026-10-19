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
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Coordinates
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.QuantumTime
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Gates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Workspace.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.Input.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.ResourceBounds
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.BankReset
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled.Counts
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

/-- Independent quantum-system allowance for one reusable bank, or zero for zero batches. -/
public def qubitBoundAtCount (N count : Nat) : Nat :=
  Recycling.Program.qubitLimit N count

/-- Independent classical allowance for the retained frame and simultaneous temporary storage. -/
public def classicalBitBoundAtCount (N count : Nat) : Nat :=
  Recycling.Program.classicalBitLimit N count

/-- Symbolic native gate ceiling for any count and gate coordinate. -/
public def gateCountBoundAtCount (N count : Nat)
    (coordinate : AlgorithmGate.Coordinate) : Nat :=
  Recycling.Program.gateCountLimit N count coordinate

/-- Independent whole-run time ceiling, with zero time for zero batches. -/
public def quantumTimeBoundAtCount (N count : Nat) : Nat :=
  Recycling.Program.quantumTimeLimit N count

/-- Symbolic ceiling for literal classical operations on the actual path. -/
public def classicalOperationBoundAtCount (N count : Nat) : Nat :=
  Recycling.Program.classicalOperationLimit N count

end

end QuantumAlg.Factoring.RSA

namespace QuantumAlg.Factoring.RSA.ScalarBounds

noncomputable section

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
  97_125_852 * modulusBits N + 3_183_480 * shortLogBits N +
    3_183_840 * tradeoffBits N + 291_374_880 * coordinateEnvelope N + 8_695_564_699


/-- Scalar envelope for chronological feedback rotations across both measured exponent registers. -/
public def feedbackEnvelope (N : Nat) : Nat :=
  (shortLogBits N + tradeoffBits N).choose 2 + (tradeoffBits N).choose 2


/-- Quantum-system envelope for one control qubit and two arithmetic words. -/
public def qubitEnvelope (N : Nat) : Nat := 1 + 2 * arithmeticBits N


/-- Both controlled MACs and the selected swap use the canonical Toffoli allowance. -/
public def toffoliEnvelope (N count : Nat) : Nat :=
  16 * count * measurementBits N *
    MAU.Multiplication.Gidney.controlledToffoliBound (arithmeticBits N)

/-- Both controlled MACs use the canonical CNOT allowance. -/
public def cnotEnvelope (N count : Nat) : Nat :=
  16 * count * measurementBits N *
    MAU.Multiplication.Gidney.controlledCnotBound (arithmeticBits N)

/-- Single-qubit gates occur only in loading, feedback, correction and reset. -/
public def singleQubitEnvelope (N count : Nat) : Nat :=
  1 + 16 * count * (3 * measurementBits N + feedbackEnvelope N + qubitEnvelope N + 1)

/-- Whole-run time uses the canonical serial allowance of the same selected multiplier. -/
public def quantumTimeEnvelope (N count : Nat) : Nat :=
  1 + 16 * count * (measurementBits N *
    (MAU.Multiplication.Gidney.controlledTimeBound (arithmeticBits N) + 3) +
      feedbackEnvelope N + 2)


/-- Whole-run scalar envelope for literal classical operations and deterministic recovery. -/
public def classicalOperationEnvelope (N count : Nat) : Nat :=
  count * (44 * modulusBits N + 182 + recoveryEventEnvelope N) + 1


/-- Whole-run scalar envelope for stored batch data and reusable classical workspace. -/
public def classicalSpaceEnvelope (N count : Nat) : Nat :=
  count * (19 * modulusBits N + 16 * measurementBits N + 2) + modulusBits N + 1 +
    measurementBits N + max (9 * modulusBits N + 14)
      (max (recoverySpaceEnvelope N + 8 * modulusBits N + 2)
        (max (qubitEnvelope N) (2 * modulusBits N + 2)))

/-- The recovery coordinate's size/log conversion is restricted to the original key carrier. -/
lemma sameBit_size_eq_clog {bitWidth : Nat} (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth)
    (positive : 1 ≤ bitWidth) :
    Nat.size pair.modulus = Nat.clog 2 pair.modulus :=
  (QuantumAlg.RSA.FixedWidthSampling.modulus_size_eq_two_mul pair positive).trans
    (QuantumAlg.RSA.FixedWidthSampling.modulus_clog_eq_two_mul pair positive).symm

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

private lemma pairAllocation_eq (N : Nat) :
    LatticePairRecoveryWorkspace.allocationBits N =
      104 * LatticeWideLllMachine.Width N + 5 * modulusBits N +
        6 * measurementBits N + 33 := by
  have combined := BatchMachine.measurementBits_eq_jkWidth N
  unfold LatticePairRecoveryWorkspace.allocationBits
  omega

private lemma quadraticAllocation_polynomial (width : Nat) :
    5 * QuadraticPrefix.discriminantWidth width +
      7 * QuadraticCandidateCheck.CandidateWidth width + QuadraticPrefix.centerWidth width +
      8 * NatSqrt.workWidth (QuadraticPrefix.discriminantWidth width) + 10 =
        34 * width + 51 := by
  simp only [QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth,
    QuadraticCandidateCheck.CandidateWidth, NatSqrt.workWidth]
  omega

private lemma quadraticAllocation_eq (N : Nat) :
    QuadraticScratchLayout.allocationBits N =
      34 * LatticePairCandidateRecovery.Width N + 51 := by
  exact quadraticAllocation_polynomial (LatticePairCandidateRecovery.Width N)

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

/-- The public recovery-space expression equals the actual allocation on original same-bit keys. -/
lemma sameBit_recoverySpaceEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth) :
    LatticeBatchRecoveryWorkspace.allocationBits pair.modulus =
      recoverySpaceEnvelope pair.modulus := by
  rw [recoveryAllocation_eq, sameBit_coordinateEnvelope_eq pair positive]; rfl

/-- Pure affine expansion of the existing recovery ceiling; no old execution proof is used. -/
lemma recoveryEventCount_affine (modulusWidth m ell coordinateWidth : Nat) :
    LatticeFixedBatchRecoveryMachine.eventCountBound modulusWidth m ell coordinateWidth =
      97_125_852 * modulusWidth + 3_183_480 * m + 3_183_840 * ell +
        291_374_880 * coordinateWidth + 8_695_564_699 := by
  norm_num [LatticeFixedBatchRecoveryMachine.eventCountBound,
    LatticeFixedBatchRecoveryMachine.nearestPlaneEnvelopeBound,
    QuantumAlg.RSA.shortLogRecoveryFuel, modularSetupCardBound, candidateScanCardBound,
    candidateScanWork, candidateSlotCardBound, quadraticGuardedCardBound, natSqrtCardBound,
    QuadraticPrefix.discriminantWidth, QuadraticPrefix.centerWidth]
  omega

/-- The displayed recovery-event ceiling is the same parameter bound on each original key. -/
lemma sameBit_recoveryEventEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth) :
    LatticeFixedBatchRecoveryMachine.eventCountBound (modulusBits pair.modulus)
      (shortLogBits pair.modulus) (tradeoffBits pair.modulus)
      (LatticePairCandidateRecovery.Width pair.modulus) = recoveryEventEnvelope pair.modulus := by
  rw [recoveryEventCount_affine]
  change 97_125_852 * modulusBits pair.modulus + 3_183_480 * shortLogBits pair.modulus +
    3_183_840 * tradeoffBits pair.modulus + 291_374_880 *
      QuantumAlg.RSA.ShortLogWidths.coordinateWidth pair.modulus
        (shortLogBits pair.modulus) (tradeoffBits pair.modulus) + 8_695_564_699 = _
  rw [sameBit_coordinateEnvelope_eq pair positive]; rfl

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
    · simp only [ShortDLP.CompiledMAU.cleanWorkspace, dif_pos positive, dif_pos fitted,
        Fin.val_zero, Nat.zero_add, Nat.FixedWidth.unitResidueWord_one_val]
      have residue : 1 % N = 0 ∨ 1 % N = 1 := by
        have bounded := Nat.mod_le 1 N
        omega
      rcases residue with zero | one
      · simp only [zero, Nat.mul_zero, true_or]
      · simp only [one, Nat.mul_one]
        exact Or.inr rfl
    · simp [ShortDLP.CompiledMAU.cleanWorkspace, positive, fitted,
        ShortDLP.CompiledMAU.zeroWorkspace]
  · simp [ShortDLP.CompiledMAU.cleanWorkspace, positive, ShortDLP.CompiledMAU.zeroWorkspace]

/-- The new single-control bank's actual seed load uses at most one X, on every total branch. -/
lemma rsaScalar_seedLoad_count_le_one (width N : Nat) :
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
  cases coordinate <;>
    simp [RSA.Recycling.Program.roundEventBudget, RSA.Recycling.Program.packingEventBudget,
      RSA.Recycling.Program.seedEventBudget, ShortDLP.CompiledMAU.Recycling.BankReset.eventBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.memberBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.baseBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.arithmeticBudget,
      ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
      ShortDLP.CompiledMAU.Recycling.Resources.oneQubit,
      ShortDLP.CompiledMAU.Recycling.Resources.oneMeasurement]
  all_goals ring

/-- Every literal initial load and reload takes at most one unit of quantum time. -/
lemma seedLoadQuantumTime_le_one (N : Nat) :
    RSA.Recycling.Program.seedLoadQuantumTime N ≤ 1 :=
  rsaScalar_seedLoad_count_le_one (arithmeticBits N) N

/-- Complete positive-count gate limits count only the actual independent quantum-gate pool. -/
lemma positive_gateCountLimit_eq (N laterCount : Nat) (coordinate : AlgorithmGate.Coordinate) :
    RSA.Recycling.Program.gateCountLimit N (laterCount + 1) coordinate =
      16 * (laterCount + 1) * ResourcePool.count (model := Model) (.gate coordinate)
        (RSA.Recycling.Program.roundEventBudget
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) +
      if coordinate = .singleQubit then
        EncodedBit.Word.BasisLoad.xCount
          (ShortDLP.CompiledMAU.Recycling.seedLabel (arithmeticBits N) N)
      else 0 := by
  have sourceZero := RecoveryNativeGates.sampler_gate_zero (model := Model) coordinate N
  have recoveryZero := RecoveryNativeGates.recovery_gate_zero (model := Model) coordinate N
  have selectionZero := RecoveryNativeGates.optional_gate_zero
    (model := Model) coordinate (modulusBits N) (laterCount + 1)
  simp only [RSA.Recycling.Program.gateCountLimit, RSA.Recycling.Program.eventBudget,
    RSA.Recycling.Program.batchEventBudget, RSA.Recycling.Program.bodyEventBudget,
    RSA.Recycling.Program.sourceEventBudget, RSA.Recycling.Program.recoveryEventBudget,
    RSA.Recycling.Program.selectionEventBudget, ResourcePool.count_add,
    ResourcePool.count_nsmul, sourceZero, recoveryZero, selectionZero, zero_add, add_zero]
  cases coordinate <;>
    (simp [RSA.Recycling.Program.preparationEventBudget, RSA.Recycling.Program.seedEventBudget];
      ring)

private lemma resultBits_parameters (N : Nat) :
    ShortDLP.CompiledMAU.Recycling.resultBits (shortLogBits N) (tradeoffBits N) =
      measurementBits N := rfl

/-- The independent positive-count pool has exactly its canonical Toffoli allowance. -/
public lemma toffoliEnvelope_eq (N laterCount : Nat) :
    RSA.gateCountBoundAtCount N (laterCount + 1) .toffoli =
      toffoliEnvelope N (laterCount + 1) := by
  change RSA.Recycling.Program.gateCountLimit N (laterCount + 1) .toffoli = _
  rw [positive_gateCountLimit_eq, round_gate_count]
  simp only [ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
    if_neg (show AlgorithmGate.Coordinate.toffoli ≠ .singleQubit by decide),
    Nat.add_zero, resultBits_parameters]
  unfold toffoliEnvelope
  ring

/-- The independent positive-count pool has exactly its canonical CNOT allowance. -/
public lemma cnotEnvelope_eq (N laterCount : Nat) :
    RSA.gateCountBoundAtCount N (laterCount + 1) .cnot =
      cnotEnvelope N (laterCount + 1) := by
  change RSA.Recycling.Program.gateCountLimit N (laterCount + 1) .cnot = _
  rw [positive_gateCountLimit_eq, round_gate_count]
  simp only [ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
    if_neg (show AlgorithmGate.Coordinate.cnot ≠ .singleQubit by decide),
    Nat.add_zero, resultBits_parameters]
  unfold cnotEnvelope
  ring

/-- Loading and peripheral gates exhaust the independent single-qubit allowance. -/
public lemma singleQubitEnvelope_le (N laterCount : Nat) :
    RSA.gateCountBoundAtCount N (laterCount + 1) .singleQubit ≤
      singleQubitEnvelope N (laterCount + 1) := by
  have load := rsaScalar_seedLoad_count_le_one (arithmeticBits N) N
  change RSA.Recycling.Program.gateCountLimit N (laterCount + 1) .singleQubit ≤ _
  rw [positive_gateCountLimit_eq, round_gate_count]
  simp only [ShortDLP.CompiledMAU.Recycling.Resources.arithmeticGateBound,
    Nat.mul_zero, Nat.zero_add, resultBits_parameters]
  have roundBound :
      3 * measurementBits N + (tradeoffBits N + shortLogBits N).choose 2 +
        (tradeoffBits N).choose 2 + (1 + 2 * arithmeticBits N) +
        EncodedBit.Word.BasisLoad.xCount
          (ShortDLP.CompiledMAU.Recycling.seedLabel (arithmeticBits N) N) ≤
      3 * measurementBits N + feedbackEnvelope N + qubitEnvelope N + 1 := by
    unfold feedbackEnvelope qubitEnvelope
    rw [Nat.add_comm (shortLogBits N) (tradeoffBits N)]
    omega
  exact (Nat.add_le_add
    (Nat.mul_le_mul_left (16 * (laterCount + 1)) roundBound) load).trans_eq
      (by unfold singleQubitEnvelope; ring)

/-- The independent time allowance retains the canonical arithmetic time and all reset/reloads. -/
public lemma quantumTimeEnvelope_le (N laterCount : Nat) :
    RSA.quantumTimeBoundAtCount N (laterCount + 1) ≤
      quantumTimeEnvelope N (laterCount + 1) := by
  have load := seedLoadQuantumTime_le_one N
  have member : RSA.Recycling.Program.memberQuantumTimeLimit N ≤
      measurementBits N *
        (MAU.Multiplication.Gidney.controlledTimeBound (arithmeticBits N) + 3) +
          feedbackEnvelope N + 2 := by
    unfold RSA.Recycling.Program.memberQuantumTimeLimit
    rw [ShortDLP.CompiledMAU.Recycling.Resources.memberTime, resultBits_parameters]
    refine (Nat.add_le_add_left load _).trans_eq ?_
    unfold feedbackEnvelope
    rw [Nat.add_comm (shortLogBits N) (tradeoffBits N)]
  exact Nat.add_le_add load (Nat.mul_le_mul_left (16 * (laterCount + 1)) member)

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

private lemma positive_classicalOperationLimit_le (N laterCount : Nat) :
    RSA.Recycling.Program.classicalOperationLimit N (laterCount + 1) ≤
      (laterCount + 1) * (44 * modulusBits N + 182 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (LatticePairCandidateRecovery.Width N)) + 1 := by
  have sourceBound := (classicalWeight_le_card
    (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope Model N)).trans_eq
      (ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card Model N)
  have recoveryBound := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
    (model := Model) N
  have selectionBound := (classicalWeight_le_card
    (FirstAccepted.Direct.Optional.Allocation.eventEnvelope Model (modulusBits N)
      (laterCount + 1))).trans_eq
      (FirstAccepted.Direct.Optional.Allocation.eventEnvelope_card
        Model (modulusBits N) (laterCount + 1))
  simp only [RSA.Recycling.Program.classicalOperationLimit, RSA.Recycling.Program.eventBudget,
    RSA.Recycling.Program.batchEventBudget, RSA.Recycling.Program.bodyEventBudget,
    RSA.Recycling.Program.sourceEventBudget, RSA.Recycling.Program.recoveryEventBudget,
    RSA.Recycling.Program.selectionEventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_nsmul, round_classicalWeight]
  simp only [RSA.Recycling.Program.preparationEventBudget, RSA.Recycling.Program.seedEventBudget,
    ResourcePool.weightedCount_nsmul, ResourcePool.weightedCount_singleton,
    Resource.Event.classicalOperationWeight, mul_zero, zero_add, Nat.mul_one]
  exact (Nat.add_le_add
    (Nat.mul_le_mul_left (laterCount + 1)
      (Nat.add_le_add sourceBound (Nat.add_le_add_left recoveryBound 16)))
    selectionBound).trans_eq (by simp only [modulusBits]; ring)

/-- Every original same-bit key has the displayed paid classical-operation ceiling. -/
private lemma sameBit_classicalOperationEnvelope_le_proof {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth)
    (laterCount : Nat) :
    RSA.Recycling.Program.classicalOperationLimit pair.modulus (laterCount + 1) ≤
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
    RSA.Recycling.Program.classicalBitLimit pair.modulus (laterCount + 1) =
      classicalSpaceEnvelope pair.modulus (laterCount + 1) := by
  rw [RSA.Recycling.Program.classicalBitLimit, RSA.Recycling.ClassicalFrame.classicalBits,
    sameBit_recoverySpaceEnvelope_eq pair positive]; rfl

public lemma sameBit_classicalSpaceEnvelope_eq {bitWidth : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bitWidth) (positive : 1 ≤ bitWidth)
    (laterCount : Nat) :
    RSA.classicalBitBoundAtCount pair.modulus (laterCount + 1) =
      classicalSpaceEnvelope pair.modulus (laterCount + 1) :=
  sameBit_classicalSpaceEnvelope_eq_proof pair positive laterCount

private lemma sameBit_positive_scalar_bounds_proof (N laterCount : Nat)
    (key : GoodKeyModel N) :
    RSA.Recycling.Program.spaceLimit N (laterCount + 1) .classicalBits =
        classicalSpaceEnvelope N (laterCount + 1) ∧
    RSA.Recycling.Program.spaceLimit N (laterCount + 1) (.quantumSystems 2) =
        qubitEnvelope N ∧
    RSA.Recycling.Program.gateCountLimit N (laterCount + 1) .toffoli =
        toffoliEnvelope N (laterCount + 1) ∧
    RSA.Recycling.Program.gateCountLimit N (laterCount + 1) .cnot =
        cnotEnvelope N (laterCount + 1) ∧
    RSA.Recycling.Program.gateCountLimit N (laterCount + 1) .singleQubit ≤
        singleQubitEnvelope N (laterCount + 1) ∧
    RSA.Recycling.Program.quantumTimeLimit N (laterCount + 1) ≤
        quantumTimeEnvelope N (laterCount + 1) ∧
    RSA.Recycling.Program.classicalOperationLimit N (laterCount + 1) ≤
        classicalOperationEnvelope N (laterCount + 1) := by
  rcases key with ⟨bitWidth, pair, rfl, effectiveRange, _⟩
  have effective : 512 ≤ bitWidth := effectiveRange
  have positive : 1 ≤ bitWidth := by omega
  have classical := sameBit_classicalSpaceEnvelope_eq_proof pair positive laterCount
  have classicalOps := sameBit_classicalOperationEnvelope_le_proof pair positive laterCount
  have qubits :
      RSA.Recycling.Program.spaceLimit pair.modulus (laterCount + 1) (.quantumSystems 2) =
        qubitEnvelope pair.modulus := by
    simpa only [RSA.Recycling.Program.qubitLimit, qubitEnvelope] using
      RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_qubits pair.modulus (laterCount + 1)
  have classicalSpace :=
    (RSA.Recycling.Program.rsaRecyclingParent_spaceLimit_classicalBits pair.modulus
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
        RSA.Recycling.Program.spaceLimit N count .classicalBits =
        base.residentSpace .classicalBits + classicalSpaceEnvelope N count ∧
    base.auxiliarySpace .classicalBits +
        RSA.Recycling.Program.spaceLimit N count .classicalBits =
        base.auxiliarySpace .classicalBits + classicalSpaceEnvelope N count ∧
    base.residentSpace (.quantumSystems 2) +
        RSA.Recycling.Program.spaceLimit N count (.quantumSystems 2) =
        base.residentSpace (.quantumSystems 2) + qubitEnvelope N ∧
    base.auxiliarySpace (.quantumSystems 2) +
        RSA.Recycling.Program.spaceLimit N count (.quantumSystems 2) =
        base.auxiliarySpace (.quantumSystems 2) + qubitEnvelope N ∧
    RSA.Recycling.Program.gateCountLimit N count .toffoli = toffoliEnvelope N count ∧
    RSA.Recycling.Program.gateCountLimit N count .cnot = cnotEnvelope N count ∧
    RSA.Recycling.Program.gateCountLimit N count .singleQubit ≤ singleQubitEnvelope N count ∧
    RSA.Recycling.Program.quantumTimeLimit N count ≤ quantumTimeEnvelope N count ∧
    RSA.Recycling.Program.classicalOperationLimit N count ≤ classicalOperationEnvelope N count
  simp only [countEq]
  exact ⟨congrArg (fun bits : Nat => base.residentSpace .classicalBits + bits) classicalSpace,
    congrArg (fun bits : Nat => base.auxiliarySpace .classicalBits + bits) classicalSpace,
    congrArg (fun bits : Nat => base.residentSpace (.quantumSystems 2) + bits) qubits,
    congrArg (fun bits : Nat => base.auxiliarySpace (.quantumSystems 2) + bits) qubits,
    toffoli, cnot, singleQubit, quantumTime, classicalOps⟩

end

end QuantumAlg.Factoring.RSA.ScalarBounds
