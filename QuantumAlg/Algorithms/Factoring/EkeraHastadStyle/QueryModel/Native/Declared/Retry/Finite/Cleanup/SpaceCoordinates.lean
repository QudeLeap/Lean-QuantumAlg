/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.SpaceArithmetic
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Space

/-!
# Independent scalar storage for the completed declared original-bank retry

Every positive count keeps the same sixteen sample slots, working result,
source parameter and three selector cells. Source preparation, reset and
complete classical recovery share the maximum of their real scratch budgets.
The single original bank contributes only dimension-two systems. Zero count
retains only the actual empty result. Caller storage is added without changing
its original resident or auxiliary role.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution
open QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.SpaceArithmetic

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
  exact bank_classical_arithmetic M d A

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
theorem declaredCleanup_additionalSpace_classicalBits (N count : Nat) :
    additionalSpace N count .classicalBits = classicalBitBound N count := by
  cases count with
  | zero =>
      simp [additionalSpace, classicalBitBound, SpacePool.ofShape, CShape.bitWidth]
      omega
  | succ count => exact positive_classical N

/-- Every native quantum dimension of the independent allowance is explicit. -/
theorem declaredCleanup_additionalSpace_quantum (N count : Nat) (dimension : ℕ+) :
    additionalSpace N count (.quantumSystems dimension) =
      if (2 : ℕ+) = dimension then qubitBound N count else 0 := by
  cases count with
  | zero => simp [additionalSpace, SpacePool.ofShape, qubitBound]
  | succ count => exact positive_quantum N dimension

/-- Same-bit prime inputs retain exactly the original oracle width at every positive count. -/
theorem declaredCleanup_qubitBound_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (laterCount : Nat) :
    qubitBound pair.modulus (laterCount + 1) = 3 * n + 2 * ((n + 2) / 2) + 1 :=
  nativeOracle_qubitCount_sameBit pair positive


variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
