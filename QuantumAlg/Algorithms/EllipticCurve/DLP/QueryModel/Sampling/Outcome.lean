/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Distribution
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Probability
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Distribution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Original Fourier outcomes on the actual intrinsic ECDLP bank

The source's raw big-endian outcomes are exactly the real retained exponent
cell observations. The point bank is neither discarded nor replaced by the
ambient group's dimension.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem

/-- Fixed physical runtime basis corresponding to a complete raw binary label. -/
@[expose] public def runtimeBasis (I : ECDLPInstance E)
    (label : Fin (2 ^ Layout.totalQubits I)) : (post I).register.Index :=
  (basisEquiv I).symm ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm label)

/-- The actual complete bank carries the original raw source amplitude. -/
public lemma ecdlpSampling_runtimeSourceState_runtimeBasis (I : ECDLPInstance E)
    (A : Access I) (label : Fin (2 ^ Layout.totalQubits I)) :
    runtimeSourceState I A (runtimeBasis I label) = sourceState I A label := by
  change sourceState I A
    ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I))
      ((basisEquiv I) ((basisEquiv I).symm
        ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm label)))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Actual exponent-cell readout is the source's big-endian Fourier outcome. -/
public lemma ecdlpSampling_basisOutcome_runtimeBasis (I : ECDLPInstance E)
    (left right : Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)))
    (tail : Fin (2 ^ Layout.pointWidth E)) :
    basisOutcome I (runtimeBasis I (rawBasis I left right tail)) =
      FiniteCyclicDLP.Canonical.BornBridge.measurementOutcome (problem I)
        (prodEquiv (left, right)) := by
  funext index
  unfold basisOutcome exponentPosition wireEquiv runtimeBasis basisEquiv
  rw [Equiv.symm_symm]
  change decide
    (((Execution.basisOfEqualWires (layout I) (post I).quantumLayout (sourceWires I)
      ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm
        (rawBasis I left right tail)))
        (Execution.positionsOfEqualWires (layout I) (post I).quantumLayout (sourceWires I)
          (Fin.castAdd (Layout.pointWidth E) index))).val = 1) = _
  rw [Execution.basisOfEqualWires_value]
  change decide
    ((((BinaryBasis.bigEndianEquiv (sampleWidth I + Layout.pointWidth E)).symm
      (prodEquiv (prodEquiv (left, right), tail)))
        (Fin.castAdd (Layout.pointWidth E) index)).val = 1) = _
  rw [BinaryBasis.bigEndianEquiv_prod_left, BinaryBasis.bigEndianEquiv_symm_value]
  have reverse : FiniteCyclicDLP.orderWidth (problem I) +
      FiniteCyclicDLP.orderWidth (problem I) - 1 - index.val = index.rev.val := by
    rw [Fin.val_rev]
    change FiniteCyclicDLP.orderWidth (problem I) +
      FiniteCyclicDLP.orderWidth (problem I) - 1 - index.val =
        FiniteCyclicDLP.orderWidth (problem I) +
          FiniteCyclicDLP.orderWidth (problem I) - (index.val + 1)
    omega
  simp only [FiniteCyclicDLP.Canonical.BornBridge.measurementOutcome, reverse]
  change decide
    ((finTwoEquiv.symm ((prodEquiv (left, right)).val.testBit index.rev.val)).val = 1) =
      (prodEquiv (left, right)).val.testBit index.rev.val
  cases (prodEquiv (left, right)).val.testBit index.rev.val <;> decide

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
