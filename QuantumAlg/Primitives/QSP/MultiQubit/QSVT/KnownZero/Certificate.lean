/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Resources
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate

/-!
# Source certificates for expanded zero-projector execution

The source phase-synthesis theorem selects the phases. Exact native expansion
preserves its target block while replacing all projector queries by counted
native gates [GSLW19, BlockHam.tex:747-887].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
noncomputable section

/-- Original matching-parity assumptions select one actual word with its exact native budget. -/
theorem exists_real_word {m n L : Nat} {PRe : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n))) (positiveSignal : 0 < n)
    (allowControlled : Bool)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (positiveDegree : 0 < L) :
    ∃ phases : List ℝ, phases.length = L ∧
      projectedPhasePlusBlock (OrthogonalProjector.zeroAncilla m n)
        (OrthogonalProjector.zeroAncilla m n)
        (circuit U positiveSignal allowControlled phases).binaryMatrix =
          singularValuePolynomial (OrthogonalProjector.zeroAncilla m n) L
            (realPolynomialToComplex PRe)
            (projectedUnitaryBlock (OrthogonalProjector.zeroAncilla m n)
              (OrthogonalProjector.zeroAncilla m n) U) ∧
      (circuit U positiveSignal allowControlled phases).eventCost = budget U allowControlled L ∧
      (circuit U positiveSignal allowControlled phases).evaluatedEventDepth (fun _ => 1) =
        (2 * (2 * m + EncodedBit.Word.OneDirtyLayout.gateCount m) + 2) * L := by
  obtain ⟨phases, length, correct, _, _⟩ := Native.exists_native_real_word U
    (OrthogonalProjector.zeroAncilla m n) (OrthogonalProjector.zeroAncilla m n)
    allowControlled source positiveDegree
  refine ⟨phases, length, ?_, ?_, ?_⟩
  · rw [circuit_matrix]
    simpa only [projectedOutputProjector, ite_self] using correct
  · rw [circuit_events, length]
  · rw [circuit_depth, length]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
