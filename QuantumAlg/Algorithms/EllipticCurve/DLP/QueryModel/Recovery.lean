/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Resources.Modulus
public import QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
public import QuantumAlg.Util.Classical.EllipticCurve.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# Actual declared-query ECDLP sampling and checked recovery

The original borrowed identity-inclusive base and target values stay in their
structural input slots. The intrinsic quantum bank, exponent cells and reset
cell are allocated once. Each prescribed round executes its real sampling
and two physical resets, then immediately performs the original complete raw
recovery, curve scalar verification and first-success update. Seven persistent
recovery cells are allocated once; one optional result is packed after the
finite loop. The secret is never an execution input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original fitted coordinate width determines every classical point cell. -/
public def fieldWidth (E : PrimeFieldShortWeierstrass p) : Nat := Layout.fieldWidth E

/-- The original oversampled Fourier width determines every recovery word. -/
public abbrev scalarWidth (I : ECDLPInstance E) : Nat := FiniteCyclicDLP.orderWidth (problem I)

/-- The actual checked arithmetic uses the original curve, field and ellipticity data. -/
public def curve (E : PrimeFieldShortWeierstrass p) :
    ClassicalAlgorithms.EllipticCurve.CurveSpec (fieldWidth E) := Layout.curveSpec E

/-- Construct the original public-order modulus from its proved capacity. -/
public def modulus (I : ECDLPInstance E) (nontrivial : 2 ≤ (problem I).order) :
    ClassicalAlgorithms.Modular.ModulusSpec (scalarWidth I) :=
  FiniteCyclicDLP.Canonical.resourceModulusSpec (problem I) nontrivial

private def originalInput {shape : CShape} (I : ECDLPInstance E)
    (input : CInputRef (Sampling.pre I) shape) :
    CInputRef (Sampling.Reuse.context I) shape :=
  (MeasurementCells.liftInput 2
    (input.underOwnedLayout (Sampling.pre I).canonicalFreshKey (layout I)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.pre I)) (Sampling.bankDisjoint I))
    (Sampling.sampleWidth I)).underRetained (Sampling.post I).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I))

/-- Keep reading the original borrowed base point beneath every sampling allocation. -/
public def baseInput (I : ECDLPInstance E) :
    CInputRef (Sampling.Reuse.context I) (.ellipticCurvePoint (fieldWidth E)) :=
  originalInput I (Runtime.Context.baseRef I)

/-- Keep reading the original borrowed target point, including the identity case. -/
public def targetInput (I : ECDLPInstance E) :
    CInputRef (Sampling.Reuse.context I) (.ellipticCurvePoint (fieldWidth E)) :=
  originalInput I (Runtime.Context.targetRef I)

/-- All original inputs, bank cells and persistent recovery destinations remain live. -/
public def post (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  batchResultCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

/-- Execute the real sampler and checked recovery in each prescribed finite round. -/
public def tail (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Circuit (Sampling.executionModel I A) (Sampling.Reuse.context I) (post I) :=
  sampledRecoveryTail (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) count (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)

/-- Allocate the same bank once, then run the actual interleaved finite recovery tail. -/
public def code (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Circuit (Sampling.executionModel I A) (Sampling.pre I) (post I) :=
  (Sampling.Reuse.initialCode I A).seq (tail I A expansion nontrivial count)

/-- The complete output reads the actual packed optional first-success result. -/
public def run (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    AlgorithmRun (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) where
  code := code I A expansion nontrivial count
  output := Output.all (post I)
    (.read (batchResultRead (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)))

/-- Every finite real run restores both original borrowed point/reference observations. -/
public theorem ecdlpRecovery_run_restoresBorrowed (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles
      (Sampling.pre I) Reference) :
    (run I A expansion nontrivial count).RestoresBorrowed original := by
  apply AlgorithmRun.restoresBorrowed_of_circuit
  intro reference history _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum (code I A expansion nontrivial count)
    (by rfl) reference state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
