/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Fourier
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Laws
import all QuantumAlg.Core.Execution.Basis.Seeded.Local
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Actual local density before intrinsic ECDLP readout

The real zero allocation and native word produce the source's pure density
on the complete physical bank, for arbitrary normalized original classical
and reference inputs. The full stored-reference law remains available.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling

noncomputable section

open QuantumAlg.Execution

attribute [local instance] Classical.decEq Classical.propDecidable

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The independent source vector on the actual ordered physical runtime bank. -/
@[expose] public def runtimeSourceState (I : ECDLPInstance E) (A : Access I) :
    NormalizedVector (post I).register :=
  NormalizedVector.reindex
    ((QuantumSignature.qubitsIndexEquiv (Layout.totalQubits I)).symm.trans (basisEquiv I).symm)
    (sourceState I A)

private theorem nativeProgram_apply_zero (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (nativeProgram I A expansion).matrix.apply
        (NormalizedVector.ket (R := (post I).register) (post I).quantumLayout.zeroLabel) =
      runtimeSourceState I A := by
  apply NormalizedVector.ext
  intro row
  change (nativeProgram I A expansion).matrix.applyVec
    (NormalizedVector.ket (R := (post I).register) (post I).quantumLayout.zeroLabel :
      HilbertVector (post I).register) row = _
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket, nativeProgram_zero_amplitude]
  rfl

/-- The actual initialized bank is a pure zero marginal; no caller seed is assumed. -/
public theorem initialCode_localDensity (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((initialCode I A).execute Reference state).quantumMarginal.marginalLeft =
      DensityOperator.ofPure
        (NormalizedVector.ket (R := (post I).register) (post I).quantumLayout.zeroLabel) := by
  apply BasisSeeded.basisSeeded_localDensity
    ((initialCode I A).execute Reference state) (post I).quantumLayout.zeroLabel
    (initialCode_seeded I A state)
  exact (Circuit.execute_mass (initialCode I A) Reference state).trans normalized

/-- Every normalized original input has the actual source density before measurement. -/
public theorem ecdlpBeforeMeasurement_localDensity (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre I) Reference ((executionModel I A).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((beforeMeasurement I A expansion).execute Reference state).quantumMarginal.marginalLeft =
      DensityOperator.ofPure (runtimeSourceState I A) := by
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.unitary_localDensity, initialCode_localDensity I A state normalized,
    ← DensityOperator.ofPure_apply, nativeProgram_apply_zero]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Sampling
