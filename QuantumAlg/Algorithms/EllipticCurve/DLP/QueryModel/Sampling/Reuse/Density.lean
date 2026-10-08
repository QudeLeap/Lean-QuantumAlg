/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
public import QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Density
import all QuantumAlg.Primitives.ZReset.Bank.Local
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Actual reused-bank density at arbitrary probability mass

The real leading reset establishes zero for every incoming state, including
zero-probability failure blocks and arbitrary reference/history correlations.
The original native query word then gives the independent source density at
that same mass. No incoming seed or normalized conditional state is assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

namespace Sampling.Reuse

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original independent source vector on this round's unchanged physical bank. -/
public def runtimeSourceState (I : ECDLPInstance E) (A : Access I) :
    NormalizedVector (context I).register := Sampling.runtimeSourceState I A

/-- Actual reset establishes pure zero even on an impossible incoming observation. -/
public theorem ecdlpReuse_reset_pure (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History)) :
    (StatePromise.pure (NormalizedVector.ket (R := (context I).register)
      (context I).quantumLayout.zeroLabel)).Holds
        ((reset I A).execute Reference state).quantumMarginal.marginalLeft :=
  ZReset.Bank.zResetBank_localDensity_pure (ecdlpReuse_qubits I) (scratch I) BitWord.model state

private theorem nativeProgram_apply_zero (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (nativeProgram I A expansion).matrix.apply
      (NormalizedVector.ket (R := (context I).register) (context I).quantumLayout.zeroLabel) =
        runtimeSourceState I A := by
  change (Sampling.nativeProgram I A expansion).matrix.apply
    (NormalizedVector.ket (R := (Sampling.post I).register)
      (Sampling.post I).quantumLayout.zeroLabel) = Sampling.runtimeSourceState I A
  exact Sampling.nativeProgram_apply_zero I A expansion

/-- The real reset and original word yield the source density at the incoming mass. -/
public theorem ecdlpReuse_beforeReadout_matrix (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History)) :
    (((reset I A).seq (Circuit.unitary (nativeProgram I A expansion))).execute
      Reference state).quantumMarginal.marginalLeft.matrix =
        state.mass • (DensityOperator.ofPure (runtimeSourceState I A)).matrix := by
  have zero := ecdlpReuse_reset_pure I A state
  change _ = _ • _ at zero
  have mass : ((reset I A).execute Reference state).quantumMarginal.marginalLeft.mass =
      state.mass := by
    rw [DensityOperator.marginalLeft_mass, ExecutionState.quantumMarginal_mass,
      Circuit.execute_mass]
  rw [mass] at zero
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal, Circuit.unitary_localDensity,
    DensityOperator.applyUnitary_matrix, zero, Matrix.mul_smul, Matrix.smul_mul]
  change state.mass •
    (DensityOperator.applyUnitary (nativeProgram I A expansion).matrix
      (DensityOperator.ofPure (NormalizedVector.ket (R := (context I).register)
        (context I).quantumLayout.zeroLabel))).matrix = _
  rw [← DensityOperator.ofPure_apply, nativeProgram_apply_zero]

/-- The terminal physical reset returns the same full bank to pure zero after every round. -/
public theorem ecdlpReuse_code_pure (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context I) Reference ((executionModel I A).HiddenState × History)) :
    (StatePromise.pure (NormalizedVector.ket (R := (context I).register)
      (context I).quantumLayout.zeroLabel)).Holds
        ((code I A expansion).execute Reference state).quantumMarginal.marginalLeft := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, Circuit.execute_seq,
    State.mapHistory_quantumMarginal, Circuit.execute_seq, State.mapHistory_quantumMarginal]
  exact ecdlpReuse_reset_pure I A _

end

end Sampling.Reuse

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
