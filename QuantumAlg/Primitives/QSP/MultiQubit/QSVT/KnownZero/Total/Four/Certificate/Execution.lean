/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Depth
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Counts

/-!
# One native execution carrying complex QSVT correctness and resources

The exact block encoding, event pool and sequential depth concern the same
actual circuit, with three transformation ancillas and the original source
ancillas. This statement retains the original unrestricted signal-width domain.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

/-- Source assumptions produce one actual normalization-four execution and its native resources. -/
theorem exists_total_complex_native_execution {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n)))
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian) (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (positiveDegree : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model
        (UnitarySource.model U true true false) (layout m n),
      ExactBlockEncoding (1 + (1 + (1 + m))) n (reassociateThree circuit.binaryMatrix)
        ((1 / 4 : ℂ) • polynomialOperator P A) ∧
      circuit.eventCost = complexBudget U (L - 1) ∧
      circuit.evaluatedEventDepth (fun _ => 1) ≤ (40 * m + 21) * L + 20 := by
  obtain ⟨phases, ra, ia, rc, ic, length, block, budget⟩ :=
    exists_total_complex_polynomial_execution U A encoding hermitian P degree
      positiveDegree bounded
  refine ⟨complexWord U phases ra ia rc ic, ?_, budget, ?_⟩
  · exact ⟨fun row column => congrFun (congrFun block row) column⟩
  · have depth := totalComplexWord_depth_le U phases ra ia rc ic
    simpa only [length, Nat.sub_add_cancel positiveDegree] using depth

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
