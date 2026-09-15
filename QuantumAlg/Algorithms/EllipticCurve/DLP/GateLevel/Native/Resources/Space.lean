/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Specification
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Specification
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Space
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Depth

/-!
# Closed space and depth formulas for the original opaque ECDLP budget

For field width `f`, exponent width `t` and the unchanged actual coefficient
width `C(u) = executionCoefficientWidth (u+1)`, put
`T = max (25*t + 9*C(t) + 16) (27*f + 9*C(f) + 15)`.
Resident classical storage is `T + 6*f + 4*t + 7` bits and auxiliary storage
is `T + 2*f + 4*t + 5` bits. Both have the same `2*t+1+2*f` qubit bank.
The difference is exactly the two borrowed public points. These are axes of
the independent specification, with no multiplication of live space by retries.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native.Specification

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open ClassicalRoutines.NumberTheory.Checked.SignedReduction

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Exact resident classical bits of the independent complete-run allowance. -/
public def residentClassicalBitLimit (I : ECDLPInstance E) : Nat :=
  max (25 * FiniteCyclicDLP.orderWidth (problem I) +
      9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth
        (FiniteCyclicDLP.orderWidth (problem I) + 1) + 16)
    (27 * Layout.fieldWidth E +
      9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth
        (Layout.fieldWidth E + 1) + 15) +
    6 * Layout.fieldWidth E + 4 * FiniteCyclicDLP.orderWidth (problem I) + 7

/-- Exact auxiliary classical bits; the original borrowed points remain resident only. -/
public def auxiliaryClassicalBitLimit (I : ECDLPInstance E) : Nat :=
  max (25 * FiniteCyclicDLP.orderWidth (problem I) +
      9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth
        (FiniteCyclicDLP.orderWidth (problem I) + 1) + 16)
    (27 * Layout.fieldWidth E +
      9 * ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth
        (Layout.fieldWidth E + 1) + 15) +
    2 * Layout.fieldWidth E + 4 * FiniteCyclicDLP.orderWidth (problem I) + 5

/-- The one original bank width, retained through every sampling and recovery round. -/
public def quantumBankWidth (I : ECDLPInstance E) : Nat :=
  2 * FiniteCyclicDLP.orderWidth (problem I) + 1 + 2 * Layout.fieldWidth E

/-- A closed unit-depth ceiling preserving the original parallel member bound. -/
public def closedDepthLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (budget : Factoring.FailureBudget) : Nat :=
  2 + retryCountForBudget I budget *
    (3 * quantumBankWidth I + B.depthBound + 1 +
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I) *
          (FiniteCyclicDLP.orderWidth (problem I) - 1) / 2 +
        FiniteCyclicDLP.orderWidth (problem I) / 2) +
      2 * FiniteCyclicDLP.orderWidth (problem I) +
      (42 * FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I) * (248 * Layout.fieldWidth E + 644) + 119))

private theorem input_resident (I : ECDLPInstance E) :
    (Runtime.Context.pre I).residentSpace =
      2 • SpacePool.ofShape (Runtime.Context.PointShape E) := by
  simp [Runtime.Context.pre, Runtime.Context.baseInputCtx, two_smul]

private theorem input_auxiliary (I : ECDLPInstance E) :
    (Runtime.Context.pre I).auxiliarySpace = 0 := by
  simp [Runtime.Context.pre, Runtime.Context.baseInputCtx]

private theorem resident_bits (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (budget : Factoring.FailureBudget) :
    SpacePool.count .classicalBits (resourceBudget I B budget).resident =
      residentClassicalBitLimit I := by
  rw [resourceBudget, recoverySpace,
    QuantumAlg.EllipticCurve.LogicalResources.recoveryTailScratchSpace_eq_bits,
    QuantumAlg.EllipticCurve.LogicalResources.persistentCellSpace_eq_bits, input_resident]
  simp [residentClassicalBitLimit, samplingSpace, sampleWidth, SpacePool.count,
    SpacePool.ofShape, Runtime.Context.PointShape, ClassicalRoutines.EllipticCurve.PointShape,
    CShape.bitWidth, SpacePool.ofQuantumLayout,
    QuantumAlg.EllipticCurve.LogicalResources.clog_two, signedWidth, xgcdWidth,
    ClassicalRoutines.NumberTheory.XGCD.PureXGCD.executionCoefficientWidth]
  omega

private theorem auxiliary_bits (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (budget : Factoring.FailureBudget) :
    SpacePool.count .classicalBits (resourceBudget I B budget).auxiliary =
      auxiliaryClassicalBitLimit I := by
  rw [resourceBudget, recoverySpace,
    QuantumAlg.EllipticCurve.LogicalResources.recoveryTailScratchSpace_eq_bits,
    QuantumAlg.EllipticCurve.LogicalResources.persistentCellSpace_eq_bits, input_auxiliary]
  simp [auxiliaryClassicalBitLimit, samplingSpace, sampleWidth, SpacePool.count,
    SpacePool.ofShape, CShape.bitWidth, SpacePool.ofQuantumLayout,
    QuantumAlg.EllipticCurve.LogicalResources.clog_two, signedWidth, xgcdWidth,
    ClassicalRoutines.NumberTheory.XGCD.PureXGCD.executionCoefficientWidth]
  omega

private theorem resident_systems (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (budget : Factoring.FailureBudget) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (resourceBudget I B budget).resident =
      if 2 = dimension then quantumBankWidth I else 0 := by
  rw [resourceBudget, recoverySpace,
    QuantumAlg.EllipticCurve.LogicalResources.recoveryTailScratchSpace_eq_bits,
    QuantumAlg.EllipticCurve.LogicalResources.persistentCellSpace_eq_bits, input_resident]
  simpa [samplingSpace, SpacePool.count, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    bankLayout, quantumBankWidth, Layout.totalQubits, Layout.pointWidth, two_mul, add_assoc]
    using QubitLayout.toQuantumLayout_dimensionCount (qubitLayout I) dimension

private theorem auxiliary_systems (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (budget : Factoring.FailureBudget) (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (resourceBudget I B budget).auxiliary =
      if 2 = dimension then quantumBankWidth I else 0 := by
  rw [resourceBudget, recoverySpace,
    QuantumAlg.EllipticCurve.LogicalResources.recoveryTailScratchSpace_eq_bits,
    QuantumAlg.EllipticCurve.LogicalResources.persistentCellSpace_eq_bits, input_auxiliary]
  simpa [samplingSpace, SpacePool.count, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    bankLayout, quantumBankWidth, Layout.totalQubits, Layout.pointWidth, two_mul, add_assoc]
    using QubitLayout.toQuantumLayout_dimensionCount (qubitLayout I) dimension

private theorem depth_closed (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (budget : Factoring.FailureBudget) :
    depthLimit I B budget ≤ closedDepthLimit I B budget := by
  have bounded := attemptDepthLimit_unit_le (kind := .quantum)
    (Layout.curveSpec E) (recoveryModulus I)
  unfold depthLimit recoveryDepthLimit reusedSampleDepthLimit sampleDepthLimit
    GateLevelResources.attemptDepthLimit closedDepthLimit quantumBankWidth
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  simp only [sampleWidth, Layout.totalQubits, Layout.pointWidth]
  omega

variable (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (budget : Factoring.FailureBudget)

/-- Exact classical resident coordinate of the independent public specification budget. -/
public theorem resourceBudget_resident_classicalBits :
    SpacePool.count .classicalBits (resourceBudget I B budget).resident =
      residentClassicalBitLimit I := resident_bits I B budget

/-- Exact classical auxiliary coordinate, with the same scratch reused across all rounds. -/
public theorem resourceBudget_auxiliary_classicalBits :
    SpacePool.count .classicalBits (resourceBudget I B budget).auxiliary =
      auxiliaryClassicalBitLimit I := auxiliary_bits I B budget

/-- The independent resident allowance has one original qubit bank and no other dimensions. -/
public theorem resourceBudget_resident_quantumSystems (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (resourceBudget I B budget).resident =
      if 2 = dimension then quantumBankWidth I else 0 := resident_systems I B budget dimension

/-- The same bank is auxiliary and remains fully included in resident space. -/
public theorem resourceBudget_auxiliary_quantumSystems (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (resourceBudget I B budget).auxiliary =
      if 2 = dimension then quantumBankWidth I else 0 := auxiliary_systems I B budget dimension

/-- Original parallel preparation and QFT depth plus all paid reset and classical dependencies. -/
public theorem depthLimit_le_closedDepthLimit :
    depthLimit I B budget ≤ closedDepthLimit I B budget := depth_closed I B budget

end

end GateLevelAttempt.Native.Specification
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
