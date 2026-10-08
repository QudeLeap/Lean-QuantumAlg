/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation



import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Workspace
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Execution.Preparation.Resources

/-!
# Every actual quantum dimension and initial preparation in declared ECDLP

Classical roles never become quantum systems. The fresh owned bank consists
of exactly the original physical qubits; each receives one actual initial
zero-preparation event, independently of the requested round count.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem original_auxiliary (I : ECDLPInstance E) :
    (Sampling.pre I).auxiliarySpace = 0 := by
  simp only [Sampling.pre, Runtime.Context.pre, Runtime.Context.baseInputCtx,
    RuntimeCtx.auxiliarySpace_addBorrowedInput, RuntimeCtx.auxiliarySpace_empty]

private theorem layout_dimensions (I : ECDLPInstance E) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (SpacePool.ofQuantumLayout (layout I)) =
      if 2 = dimension then Layout.totalQubits I else 0 := by
  change (QuantumLayout.uniform (Layout.totalQubits I) 2 Fin.val
    Fin.val_injective).dimensionCount dimension = _
  exact QuantumLayout.dimensionCount_uniform (Layout.totalQubits I) 2 dimension
    Fin.val Fin.val_injective

/-- The complete independent inventories contain only the original physical qubits. -/
public theorem whole_memory_quantum_coordinates (I : ECDLPInstance E) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (tailResidentBudget I) =
        (if 2 = dimension then Layout.totalQubits I else 0) ∧
    SpacePool.count (.quantumSystems dimension) (tailAuxiliaryBudget I) =
        (if 2 = dimension then Layout.totalQubits I else 0) := by
  simp only [tailResidentBudget, tailAuxiliaryBudget, recoveryTailScratchSpace_eq_bits,
    persistentCellSpace_eq_bits, Sampling.Reuse.ecdlpReuse_context_resident,
    Sampling.Reuse.ecdlpReuse_context_auxiliary, Sampling.post_residentSpace,
    Sampling.post_auxiliarySpace, original_auxiliary]
  suffices remaining :
      SpacePool.count (.quantumSystems dimension) (SpacePool.ofQuantumLayout (layout I)) =
        (if 2 = dimension then Layout.totalQubits I else 0) by
    simpa [SpacePool.count, SpacePool.ofShape, Sampling.pre, Runtime.Context.pre,
      Runtime.Context.baseInputCtx] using remaining
  exact layout_dimensions I dimension

/-- Every owned system emits its actual zero-preparation event once at allocation. -/
public theorem whole_initialization_budget (I : ECDLPInstance E) (A : Access I) :
    initializationBudget I A = Layout.totalQubits I •
      ResourcePool.singleton (model := Sampling.executionModel I A)
        (.preparation (2 : ℕ+)) := by
  exact ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model (model I A)
    (layout I) 2 (fun _ => rfl) BitWord.model .empty

/-- The real tagged point and two exponent registers have the scalar physical width. -/
public theorem original_qubits_scalar (I : ECDLPInstance E) :
    Layout.totalQubits I = Scalar.qubits (fieldWidth E) (scalarWidth I) := by
  change scalarWidth I + scalarWidth I + (1 + 2 * fieldWidth E) = _
  unfold Scalar.qubits
  omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
