/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space

/-!
# Scalar space budgets for every finite total batch count

The displayed formulas are exact projections of the accepted independent
space allowance. Actual resident and auxiliary peaks are bounded by that
allowance on the same execution path. Persistent classical batch results
accumulate, while all positive counts use one quantum bank. Zero batches
allocate only the real empty optional result.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution ShortDLP.CompiledMAU

noncomputable section

/-- Independent classical capacity includes all retained batches and one temporary allowance. -/
public def classicalBitBound (N : Nat) : Nat → Nat
  | 0 => modulusBits N + 1
  | count + 1 =>
      LatticeBatchRecoveryWorkspace.allocationBits N + 36 * modulusBits N +
        17 * measurementBits N + 19 +
          (count + 1) * (19 * modulusBits N + 16 * measurementBits N + 2)

/-- Positive batch counts share the sole actual bank; the empty branch allocates no qubits. -/
public def qubitBound (N : Nat) : Nat → Nat
  | 0 => 0
  | _ + 1 => shortLogBits N + 2 * tradeoffBits N + 2 * arithmeticBits N

private theorem first_classical (N : Nat) :
    NativeBatchRecovery.additionalSpace N .classicalBits =
      LatticeBatchRecoveryWorkspace.allocationBits N + 36 * modulusBits N +
        17 * measurementBits N + 19 := by
  have binaryBits : Nat.clog 2 2 = 1 := by decide
  simp [NativeBatchRecovery.additionalSpace, NativeBatchRecovery.tailAdditionalSpace,
    NativeBatch.additionalSpace, ShorStyle.Canonical.Sampler.Retained.additionalSpace,
    LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    ClassicalRoutines.Modular.NativePower.powerSpace, LatticeBatchRecoveryOutput.OutputShape,
    SpacePool.ofShape, SpacePool.ofQuantumLayout, binaryBits]
  simp only [BatchMachine.JWidth, BatchMachine.KWidth]
  omega

private theorem later_classical (N : Nat) :
    NativeBatchReuseRecovery.additionalSpace N .classicalBits =
      LatticeBatchRecoveryWorkspace.allocationBits N + 36 * modulusBits N +
        16 * measurementBits N + 19 := by
  simp [NativeBatchReuseRecovery.additionalSpace, NativeBatchReuseRecovery.tailAdditionalSpace,
    NativeBatchReuse.additionalSpace, LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    ClassicalRoutines.Modular.NativePower.powerSpace, LatticeBatchRecoveryOutput.OutputShape,
    SpacePool.ofShape]
  omega

private theorem first_retained_classical (N : Nat) :
    NativeBatchRecovery.retainedSpace N .classicalBits =
      measurementBits N + NativeBatchReuseRecovery.retainedBits N := by
  have binaryBits : Nat.clog 2 2 = 1 := by decide
  simp [NativeBatchRecovery.retainedSpace, NativeBatchRecovery.bankSpace,
    NativeBatchReuseRecovery.retainedSpace_bits, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    binaryBits]

private theorem first_quantum (N : Nat) (dimension : ℕ+) :
    NativeBatchRecovery.additionalSpace N (.quantumSystems dimension) =
      (runtimeLayout (shortLogBits N) (tradeoffBits N)
        (arithmeticBits N)).dimensionCount dimension := by
  simp [NativeBatchRecovery.additionalSpace, NativeBatchRecovery.tailAdditionalSpace,
    NativeBatch.additionalSpace, ShorStyle.Canonical.Sampler.Retained.additionalSpace,
    LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    ClassicalRoutines.Modular.NativePower.powerSpace, SpacePool.ofShape,
    SpacePool.ofQuantumLayout]

private theorem later_quantum (N : Nat) (dimension : ℕ+) :
    NativeBatchReuseRecovery.additionalSpace N (.quantumSystems dimension) = 0 := by
  simp [NativeBatchReuseRecovery.additionalSpace, NativeBatchReuseRecovery.tailAdditionalSpace,
    NativeBatchReuse.additionalSpace, LatticeFixedBatchRecoveryMachine.additionalSpace,
    LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    ClassicalRoutines.Modular.NativePower.powerSpace, SpacePool.ofShape]

private theorem chain_allowance (N count : Nat) :
    NativeRetryChain.additionalSpace N count =
      NativeBatchRecovery.retainedSpace N + NativeRetryChain.suffixAllowance N count := by
  unfold NativeRetryChain.additionalSpace
  apply SpacePool.max_eq_right
  intro axis
  cases axis with
  | classicalBits =>
      simp only [Pi.add_apply, NativeRetryChain.suffixAllowance, Pi.smul_apply,
        first_classical, later_classical, first_retained_classical,
        NativeBatchReuseRecovery.retainedSpace_bits, SpacePool.ofShape, CShape.bitWidth,
        smul_eq_mul]
      omega
  | quantumSystems dimension =>
      simp [Pi.add_apply, NativeRetryChain.suffixAllowance, first_quantum, later_quantum,
        NativeBatchRecovery.retainedSpace, NativeBatchRecovery.bankSpace,
        NativeBatchReuseRecovery.retainedSpace_quantum, SpacePool.ofShape,
        SpacePool.ofQuantumLayout]

private theorem selected_allowance (N count : Nat) :
    NativeRetrySelection.additionalSpace N count = NativeRetryChain.additionalSpace N count := by
  unfold NativeRetrySelection.additionalSpace
  apply SpacePool.max_eq_left
  rw [chain_allowance]
  intro axis
  cases axis with
  | classicalBits =>
      simp only [Pi.add_apply, NativeRetryChain.retainedSpace, NativeRetryChain.suffixAllowance,
        NativeRetrySelection.tailAdditionalSpace, NativeRetrySelection.outputSpace_bits,
        ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation.scratchSpace,
        Pi.smul_apply, later_classical, first_retained_classical,
        NativeBatchReuseRecovery.retainedSpace_bits, SpacePool.ofShape, CShape.bitWidth,
        smul_eq_mul]
      omega
  | quantumSystems dimension =>
      simp [Pi.add_apply, NativeRetryChain.retainedSpace, NativeRetryChain.suffixAllowance,
        NativeRetrySelection.tailAdditionalSpace_quantum, later_quantum,
        NativeBatchReuseRecovery.retainedSpace_quantum]

/-- The zero and positive formulas equal the classical coordinate of the accepted allowance. -/
theorem additionalSpace_classicalBits (N totalRounds : Nat) :
    additionalSpace N totalRounds .classicalBits = classicalBitBound N totalRounds := by
  cases totalRounds with
  | zero => rfl
  | succ count =>
      rw [additionalSpace_succ, selected_allowance, chain_allowance]
      simp only [Pi.add_apply, NativeRetryChain.suffixAllowance, Pi.smul_apply,
        first_retained_classical, later_classical, NativeBatchReuseRecovery.retainedSpace_bits,
        SpacePool.ofShape, CShape.bitWidth, smul_eq_mul, classicalBitBound,
        NativeBatchReuseRecovery.retainedBits, Nat.add_mul, Nat.one_mul]
      omega

/-- Every positive count charges precisely the actual bank in every quantum dimension. -/
theorem additionalSpace_succ_quantum_layout (N count : Nat) (dimension : ℕ+) :
    additionalSpace N (count + 1) (.quantumSystems dimension) =
      (runtimeLayout (shortLogBits N) (tradeoffBits N)
        (arithmeticBits N)).dimensionCount dimension := by
  simp [additionalSpace_succ, NativeRetrySelection.additionalSpace,
    NativeRetryChain.additionalSpace, NativeRetryChain.suffixAllowance,
    NativeRetryChain.retainedSpace, NativeBatchRecovery.retainedSpace,
    NativeBatchRecovery.bankSpace, NativeBatchReuseRecovery.retainedSpace_quantum,
    NativeRetrySelection.tailAdditionalSpace_quantum, first_quantum, later_quantum,
    SpacePool.max, SpacePool.ofShape, SpacePool.ofQuantumLayout]

/-- The sole positive-count bank contains exactly the independently stated number of qubits. -/
theorem additionalSpace_qubits (N totalRounds : Nat) :
    additionalSpace N totalRounds (.quantumSystems 2) = qubitBound N totalRounds := by
  cases totalRounds with
  | zero => rfl
  | succ count =>
      rw [additionalSpace_succ_quantum_layout]
      rw [shortDLP_runtimeLayout_eq_source]
      simp only [QubitLayout.toQuantumLayout_dimensionCount, ↓reduceIte,
        totalQubits_eq, qubitBound]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Actual code resident classical bits obey the scalar formula on the same path. -/
theorem code_resident_classicalBits_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).peakResidentSpace path .classicalBits ≤
      base.residentSpace .classicalBits + classicalBitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_classicalBits] using
    code_resident_le base noQuantum input totalRounds path .classicalBits

/-- Actual code auxiliary classical bits obey the same independent scalar capacity. -/
theorem code_auxiliary_classicalBits_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).peakAuxiliarySpace path .classicalBits ≤
      base.auxiliarySpace .classicalBits + classicalBitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_classicalBits] using
    code_auxiliary_le base noQuantum input totalRounds path .classicalBits

/-- Actual code resident qubits include at most the one positive-count bank. -/
theorem code_resident_qubits_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).peakResidentSpace path (.quantumSystems 2) ≤
      base.residentSpace (.quantumSystems 2) + qubitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_qubits] using
    code_resident_le base noQuantum input totalRounds path (.quantumSystems 2)

/-- Actual code auxiliary qubits include at most the same single bank. -/
theorem code_auxiliary_qubits_le (input : Input N) (totalRounds : Nat)
    (path : (code base noQuantum input totalRounds).Path) :
    (code base noQuantum input totalRounds).peakAuxiliarySpace path (.quantumSystems 2) ≤
      base.auxiliarySpace (.quantumSystems 2) + qubitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_qubits] using
    code_auxiliary_le base noQuantum input totalRounds path (.quantumSystems 2)

/-- Every complete run path has the same independent resident classical-bit bound. -/
theorem run_resident_classicalBits_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.peakResidentSpace path .classicalBits ≤
      base.residentSpace .classicalBits + classicalBitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_classicalBits] using
    run_resident_le base noQuantum input totalRounds path .classicalBits

/-- Every complete run path has the same independent auxiliary classical-bit bound. -/
theorem run_auxiliary_classicalBits_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.peakAuxiliarySpace path .classicalBits ≤
      base.auxiliarySpace .classicalBits + classicalBitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_classicalBits] using
    run_auxiliary_le base noQuantum input totalRounds path .classicalBits

/-- Complete actual run resident qubits are bounded without multiplying the bank by retries. -/
theorem run_resident_qubits_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.peakResidentSpace path (.quantumSystems 2) ≤
      base.residentSpace (.quantumSystems 2) + qubitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_qubits] using
    run_resident_le base noQuantum input totalRounds path (.quantumSystems 2)

/-- Complete actual run auxiliary qubits obey the same bank bound, including zero batches. -/
theorem run_auxiliary_qubits_le (input : Input N) (totalRounds : Nat)
    (path : (run base noQuantum input totalRounds).code.Path) :
    (run base noQuantum input totalRounds).code.peakAuxiliarySpace path (.quantumSystems 2) ≤
      base.auxiliarySpace (.quantumSystems 2) + qubitBound N totalRounds := by
  simpa only [Pi.add_apply, additionalSpace_qubits] using
    run_auxiliary_le base noQuantum input totalRounds path (.quantumSystems 2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
