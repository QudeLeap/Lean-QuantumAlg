/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.QuantumTime
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Space
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Scalar coordinates of the actual recycled RSA parent

Every scalar ceiling is a projection of an independent parameter-only event
or space formula. The same actual path supplies all observations. No scalar
budget projects a candidate run, and no assumption about a good key is needed.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

private abbrev Model := ShortDLP.CompiledMAU.Recycling.model

/-- Positive execution uses one control and the two original arithmetic words. -/
def qubitLimit (N : Nat) : Nat → Nat
  | 0 => 0
  | _ + 1 => 1 + 2 * arithmeticBits N

/-- The full simultaneous classical capacity includes the complete preallocated frame. -/
def classicalBitLimit (N : Nat) : Nat → Nat
  | 0 => modulusBits N + 1
  | laterCount + 1 =>
      ClassicalFrame.classicalBits N (laterCount + 1) + measurementBits N +
        max (9 * modulusBits N + 14)
          (max (LatticeBatchRecoveryWorkspace.allocationBits N + 8 * modulusBits N + 2)
            (max (1 + 2 * arithmeticBits N) (2 * modulusBits N + 2)))

/-- Native gate ceilings observe only the independent complete event allowance. -/
def gateCountLimit (N count : Nat) (coordinate : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count (model := Model) (.gate coordinate) (eventBudget N count)

/-- Literal classical operations remain charged even though they have zero quantum duration. -/
def classicalOperationLimit (N count : Nat) : Nat :=
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight (eventBudget N count)

private lemma recoveryScratch_classicalBits (N : Nat) :
    recoveryScratch N .classicalBits =
      LatticeBatchRecoveryWorkspace.allocationBits N + 8 * modulusBits N + 2 := by
  simp [recoveryScratch, LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    Modular.NativePower.powerSpace, SpacePool.ofShape, CShape.bitWidth]
  omega

/-- The scalar classical formula is exactly the independent native space allowance. -/
lemma rsaRecyclingParent_spaceLimit_classicalBits (N count : Nat) :
    spaceLimit N count .classicalBits = classicalBitLimit N count := by
  cases count with
  | zero => rfl
  | succ laterCount =>
      change liveSpace N (laterCount + 1) .classicalBits +
        temporarySpace N .classicalBits = _
      rw [rsaRecyclingParent_liveSpace_classicalBits,
        rsaRecyclingParent_temporarySpace_classicalBits, recoveryScratch_classicalBits]
      rfl

private lemma temporarySpace_quantum (N : Nat) (dimension : ℕ+) :
    temporarySpace N (.quantumSystems dimension) = 0 := by
  simp [temporarySpace, samplerScratch, recoveryScratch, bankResetScratch, selectorScratch,
    LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    Modular.NativePower.powerSpace, SpacePool.max, SpacePool.ofShape]

/-- The positive allowance contains exactly the one actual bank at the qubit coordinate. -/
lemma rsaRecyclingParent_spaceLimit_qubits (N count : Nat) :
    spaceLimit N count (.quantumSystems 2) = qubitLimit N count := by
  cases count with
  | zero => rfl
  | succ laterCount =>
      simp only [spaceLimit, Pi.add_apply, temporarySpace_quantum]
      simp [liveSpace, ClassicalFrame.rsaRecyclingFrame_frameSpace_eq,
        bankSpace, readoutSpace, SpacePool.ofShape, SpacePool.ofQuantumLayout,
        ShortDLP.CompiledMAU.Recycling.Arithmetic.layout, QubitLayout.toQuantum,
        QuantumSignature.place, QuantumSignature.qubits,
        QuantumLayout.dimensionCount, QuantumLayout.dimensions,
        ShortDLP.CompiledMAU.Recycling.Arithmetic.width_eq, qubitLimit]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  {N : Nat} (input : Input N) (count : Nat)

/-- Every actual path obeys the same independently specified native gate coordinate. -/
lemma rsaRecyclingParent_run_gateCount_le
    (path : (run base noQuantum N input count).code.Path)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate coordinate)
      ((run base noQuantum N input count).code.resourcePool path) ≤
        gateCountLimit N count coordinate :=
  ResourcePool.le_iff_count.mp
    (rsaRecyclingParent_run_pool_le base noQuantum N input count path) (.gate coordinate)

/-- The actual resident qubit peak counts the caller and the single shared bank. -/
lemma rsaRecyclingParent_run_resident_qubits_le
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakResidentSpace path (.quantumSystems 2) ≤
      base.residentSpace (.quantumSystems 2) + qubitLimit N count := by
  simpa only [Pi.add_apply, rsaRecyclingParent_spaceLimit_qubits] using
    rsaRecyclingParent_run_resident_le base noQuantum N input count path (.quantumSystems 2)

/-- All original resident classical cells remain included in the same path bound. -/
lemma rsaRecyclingParent_run_resident_classicalBits_le
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakResidentSpace path .classicalBits ≤
      base.residentSpace .classicalBits + classicalBitLimit N count := by
  simpa only [Pi.add_apply, rsaRecyclingParent_spaceLimit_classicalBits] using
    rsaRecyclingParent_run_resident_le base noQuantum N input count path .classicalBits

/-- Auxiliary roles retain their separate caller contribution and full temporary allowance. -/
lemma rsaRecyclingParent_run_auxiliary_classicalBits_le
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakAuxiliarySpace path .classicalBits ≤
      base.auxiliarySpace .classicalBits + classicalBitLimit N count := by
  simpa only [Pi.add_apply, rsaRecyclingParent_spaceLimit_classicalBits] using
    rsaRecyclingParent_run_auxiliary_le base noQuantum N input count path .classicalBits

/-- Every paid classical operation belongs to the complete independent event allowance. -/
lemma rsaRecyclingParent_run_classicalOperation_le
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum N input count).code.resourcePool path) ≤
        classicalOperationLimit N count :=
  ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (rsaRecyclingParent_run_pool_le base noQuantum N input count path)

end

end QuantumAlg.Factoring.RSA.Recycling.Program
