/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Real
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Coverage
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Coverage
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Phases
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis

/-!
# Source certificates for the native projected circuit

The source matching-parity hypotheses choose phases and prove the target block
of the independently constructed native circuit. Its exact query pool and
sequential depth belong to that very circuit [GSLW19, BlockHam.tex:747-887].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native
noncomputable section

/-- A positive-degree real source certificate gives correctness of the actual native word. -/
theorem circuit_of_real_certificate {width L : Nat} {PRe : Polynomial ℝ}
    (U : UnitaryOperator (Qubits width)) (left right : OrthogonalProjector width)
    (allowControlled : Bool)
    (certificate : ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate L PRe)
    (positive : 0 < L) :
    projectedPhasePlusBlock (projectedOutputProjector left right L) right
      (circuit U left right allowControlled
        (projectedPhasesFromQSPCertificate
          certificate.certificate.φ₀ certificate.certificate.φs)).binaryMatrix =
      singularValuePolynomial right L (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U) := by
  obtain ⟨init, last, split⟩ := certificate.certificate.exists_init_last_of_pos positive
  let coverage :=
    sourceSingularInvariantLocalBasisSpanCoverageOfProjectorComplementSplit left right U
  exact circuit_real_correctness U left right allowControlled L
    certificate.completion.P (conjP certificate.completion.P) (realPolynomialToComplex PRe)
    (projectedPhasesFromQSPCertificate certificate.certificate.φ₀ certificate.certificate.φs)
    (sourceProjectedQSVTBlockCorrectness_of_localBasisSpanCoverage U left right
      certificate.certificate certificate.completion.qsp_pair.parP coverage init last split)
    (sourceProjectedQSVTBlockCorrectness_negProjectedPhases_of_localBasisSpanCoverage
      U left right certificate.certificate certificate.completion.qsp_pair.parP
      coverage init last split)
    (singularValuePolynomial_average_of_polynomial_average right L
      certificate.completion.P (conjP certificate.completion.P)
      (realPolynomialToComplex PRe) (projectedUnitaryBlock left right U)
      certificate.completion.average_conj_eq)

/-- Original source hypotheses yield one phase list with correctness, exact events and depth. -/
theorem exists_native_real_word {width L : Nat} {PRe : Polynomial ℝ}
    (U : UnitaryOperator (Qubits width)) (left right : OrthogonalProjector width)
    (allowControlled : Bool)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (positive : 0 < L) :
    ∃ phases : List ℝ, phases.length = L ∧
      projectedPhasePlusBlock (projectedOutputProjector left right L) right
        (circuit U left right allowControlled phases).binaryMatrix =
          singularValuePolynomial right L (realPolynomialToComplex PRe)
            (projectedUnitaryBlock left right U) ∧
      (circuit U left right allowControlled phases).eventCost =
        budget U left right allowControlled L ∧
      (circuit U left right allowControlled phases).evaluatedEventDepth (fun _ => 1) =
        4 * L := by
  let certificate :=
    ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses source
  let phases := projectedPhasesFromQSPCertificate
    certificate.certificate.φ₀ certificate.certificate.φs
  have length : phases.length = L := by
    exact (projectedPhasesFromQSPCertificate_length _ _).trans certificate.certificate.length_eq
  refine ⟨phases, length, circuit_of_real_certificate U left right allowControlled
    certificate positive, ?_, ?_⟩
  · rw [circuit_events, length]
  · rw [circuit_depth, length]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Native
