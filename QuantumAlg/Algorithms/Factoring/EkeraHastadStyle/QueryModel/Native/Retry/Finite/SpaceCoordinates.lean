/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space

/-!
# Independent scalar storage for the original-bank finite retry

Every positive count keeps the same sixteen sample slots, working result,
source parameter and three selector cells. Source preparation, reset and
complete classical recovery share the maximum of their real scratch budgets.
The single original bank contributes only dimension-two systems. Zero count
retains only the actual empty result. Caller storage is added without changing
its original resident or auxiliary role.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite

open Execution

noncomputable section

/-- The fixed original samples and selector coexist with the largest real temporary workspace. -/
public def classicalBitBound (N : Nat) : Nat → Nat
  | 0 => modulusBits N + 1
  | _ + 1 => 21 * modulusBits N + 18 * measurementBits N + 4 +
      max (9 * modulusBits N + 14)
        (LatticeBatchRecoveryWorkspace.allocationBits N + 8 * modulusBits N + 2)

/-- Positive counts share the original one-bank width; zero count allocates no quantum system. -/
public def qubitBound (N : Nat) : Nat → Nat
  | 0 => 0
  | _ + 1 => ShortDLP.totalQubits (parameters N)

private theorem classical_arithmetic (M d A : Nat) :
    d + d * 1 + 0 + (1 + M + 16 * d + (18 * M + 1)) +
        ((9 * M + 14).max 1).max (A + (8 * M + 2)) + (1 + M + (M + 1)) =
      21 * M + 18 * d + 4 + max (9 * M + 14) (A + 8 * M + 2) := by
  change d + d * 1 + 0 + (1 + M + 16 * d + (18 * M + 1)) +
    max (max (9 * M + 14) 1) (A + (8 * M + 2)) + (1 + M + (M + 1)) = _
  rw [Nat.max_eq_left (by omega : 1 ≤ 9 * M + 14)]
  rw [show A + (8 * M + 2) = A + 8 * M + 2 by omega]
  omega

private def spaceExpression (M d : Nat) (allocated bank : SpacePool .quantum) :
    SpacePool .quantum :=
  (SpacePool.ofShape (.bits d) + d • SpacePool.ofShape (.finite 2) + bank +
    (SpacePool.ofShape (.option (.unsignedWord M)) + 16 • SpacePool.ofShape (.bits d) +
      ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum M)) +
    SpacePool.max
      (SpacePool.max (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum M)
        (SpacePool.ofShape (.finite 2)))
      (allocated + ClassicalRoutines.Modular.NativePower.powerSpace .quantum M) +
    (SpacePool.ofShape (.product .bit (.unsignedWord M)) +
      (SpacePool.ofShape (.unsignedWord M) + SpacePool.ofShape .bit))

private theorem spaceExpression_classical (M d A : Nat) {count : Nat}
    (bank : QuantumLayout count) :
    spaceExpression M d (SpacePool.ofShape (.bits A)) (SpacePool.ofQuantumLayout bank)
        .classicalBits =
      21 * M + 18 * d + 4 + max (9 * M + 14) (A + 8 * M + 2) := by
  have binaryBits : Nat.clog 2 2 = 1 := by decide
  simp only [spaceExpression, ShorStyle.Canonical.Sampler.Retained.resultSpace,
    ShorStyle.Canonical.Sampler.Program.additionalSpace,
    ClassicalRoutines.Modular.NativePower.powerSpace, SpacePool.ofShape,
    SpacePool.ofQuantumLayout, SpacePool.max, Pi.add_apply, Pi.smul_apply,
    CShape.bitWidth, PNat.val_ofNat, binaryBits, smul_eq_mul]
  exact classical_arithmetic M d A

private theorem spaceExpression_quantum (M d A : Nat) {count : Nat}
    (bank : QuantumLayout count) (dimension : ℕ+) :
    spaceExpression M d (SpacePool.ofShape (.bits A)) (SpacePool.ofQuantumLayout bank)
        (.quantumSystems dimension) = bank.dimensionCount dimension := by
  simp [spaceExpression, ShorStyle.Canonical.Sampler.Retained.resultSpace,
    ShorStyle.Canonical.Sampler.Program.additionalSpace,
    ClassicalRoutines.Modular.NativePower.powerSpace, SpacePool.ofShape,
    SpacePool.ofQuantumLayout, SpacePool.max]

private theorem additionalSpace_expression (N : Nat) :
    Retry.additionalSpace N = spaceExpression (modulusBits N) (measurementBits N)
      (LatticeBatchRecoveryWorkspace.allocationSpace N) (SpacePool.ofQuantumLayout (layout N)) :=
  rfl

private theorem positive_classical (N : Nat) :
    Retry.additionalSpace N .classicalBits = classicalBitBound N 1 := by
  rw [additionalSpace_expression, LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits]
  exact spaceExpression_classical (modulusBits N) (measurementBits N)
    (LatticeBatchRecoveryWorkspace.allocationBits N) (layout N)

private theorem positive_quantum (N : Nat) (dimension : ℕ+) :
    Retry.additionalSpace N (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then ShortDLP.totalQubits (parameters N) else 0 := by
  rw [additionalSpace_expression, LatticeBatchRecoveryWorkspace.batchAllocationSpace_eq_bits,
    spaceExpression_quantum]
  exact QubitLayout.toQuantumLayout_dimensionCount (ShortDLP.layout (parameters N)) dimension

/-- Exact classical projection of the independent finite storage allowance. -/
theorem nativeOracle_finiteRetry_additionalSpace_classicalBits (N count : Nat) :
    additionalSpace N count .classicalBits = classicalBitBound N count := by
  cases count with
  | zero => rfl
  | succ count => exact positive_classical N

/-- Every native quantum dimension of the independent allowance is explicit. -/
theorem nativeOracle_finiteRetry_additionalSpace_quantum (N count : Nat) (dimension : ℕ+) :
    additionalSpace N count (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then qubitBound N count else 0 := by
  cases count with
  | zero => simp [additionalSpace, NativeRetryEmpty.additionalSpace, SpacePool.ofShape, qubitBound]
  | succ count => exact positive_quantum N dimension

/-- Same-bit prime inputs retain exactly the original oracle width at every positive count. -/
theorem nativeOracle_finiteRetry_qubitBound_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (laterCount : Nat) :
    qubitBound pair.modulus (laterCount + 1) = 3 * n + 2 * ((n + 2) / 2) + 1 :=
  nativeOracle_qubitCount_sameBit pair positive

attribute [local irreducible] run code context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The actual resident classical peak is bounded by the complete independent bit formula. -/
theorem nativeOracle_finiteRetry_resident_classicalBits_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakResidentSpace path .classicalBits ≤
      classicalBitBound N count + base.residentSpace .classicalBits := by
  have bounds := nativeOracle_finiteRetry_peakResidentSpace_le base noQuantum N input count
  rw [← nativeOracle_finiteRetry_run_code base noQuantum N input count] at bounds
  exact (bounds path .classicalBits).trans_eq
    (congrArg (· + base.residentSpace .classicalBits)
      (nativeOracle_finiteRetry_additionalSpace_classicalBits N count))

/-- Auxiliary classical storage retains the caller's original role and all real temporary bits. -/
theorem nativeOracle_finiteRetry_auxiliary_classicalBits_le (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakAuxiliarySpace path .classicalBits ≤
      classicalBitBound N count + base.auxiliarySpace .classicalBits := by
  have bounds := nativeOracle_finiteRetry_peakAuxiliarySpace_le base noQuantum N input count
  rw [← nativeOracle_finiteRetry_run_code base noQuantum N input count] at bounds
  exact (bounds path .classicalBits).trans_eq
    (congrArg (· + base.auxiliarySpace .classicalBits)
      (nativeOracle_finiteRetry_additionalSpace_classicalBits N count))

/-- Each actual resident quantum coordinate is bounded by the same original-bank allowance. -/
theorem nativeOracle_finiteRetry_resident_quantum_le (input : Input N) (count : Nat)
    (dimension : ℕ+) (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakResidentSpace path (.quantumSystems dimension) ≤
      (if (2 : ℕ+) = dimension then qubitBound N count else 0) +
        base.residentSpace (.quantumSystems dimension) := by
  have bounds := nativeOracle_finiteRetry_peakResidentSpace_le base noQuantum N input count
  rw [← nativeOracle_finiteRetry_run_code base noQuantum N input count] at bounds
  exact (bounds path (.quantumSystems dimension)).trans_eq
    (congrArg (· + base.residentSpace (.quantumSystems dimension))
      (nativeOracle_finiteRetry_additionalSpace_quantum N count dimension))

/-- Auxiliary quantum coordinates retain all real systems with their original caller roles. -/
theorem nativeOracle_finiteRetry_auxiliary_quantum_le (input : Input N) (count : Nat)
    (dimension : ℕ+) (path : (run base noQuantum N input count).code.Path) :
    (run base noQuantum N input count).code.peakAuxiliarySpace path (.quantumSystems dimension) ≤
      (if (2 : ℕ+) = dimension then qubitBound N count else 0) +
        base.auxiliarySpace (.quantumSystems dimension) := by
  have bounds := nativeOracle_finiteRetry_peakAuxiliarySpace_le base noQuantum N input count
  rw [← nativeOracle_finiteRetry_run_code base noQuantum N input count] at bounds
  exact (bounds path (.quantumSystems dimension)).trans_eq
    (congrArg (· + base.auxiliarySpace (.quantumSystems dimension))
      (nativeOracle_finiteRetry_additionalSpace_quantum N count dimension))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite
