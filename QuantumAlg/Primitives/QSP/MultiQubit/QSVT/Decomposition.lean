/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
public import QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
import all QuantumAlg.Components.Oracle.ProjectedSignal
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Actual projected QSVT realizations

The source matching-parity theorem is implemented by the typed alternating
word. Its source, inverse-source and projector queries are granted by the
Problem's access model; native rotations, events, space and depth are derived
from the same physical circuit [GSLW19, BlockHam.tex:747-890].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT
noncomputable section

/-- Independent source and native event budget of the length-L projected implementation. -/
public def projectedEventBudget (N L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (ProjectedSignal.model N)) :=
  let pool : Resource.Event
      (.quantum AlgorithmGate.model (ProjectedSignal.model N)) →
      ResourcePool (.quantum AlgorithmGate.model (ProjectedSignal.model N)) :=
    ResourcePool.singleton
  ((L + 1) / 2) • pool (.oracle (.source .ordinary)) +
    (L / 2) • pool (.oracle (.source .inverse)) +
    (2 * ((L + 1) / 2)) • pool (.oracle .leftNot) +
    (2 * (L / 2)) • pool (.oracle .rightNot) +
    L • pool (.gate .singleQubit)

namespace ProjectedEventProfile

/-- Exact same-circuit event equality in the declared projected-signal model. -/
public def HasExactCounts (N L : Nat)
    (events : ResourcePool (.quantum AlgorithmGate.model (ProjectedSignal.model N))) :
    Prop := events = projectedEventBudget N L

end ProjectedEventProfile

/-- Same-circuit realization of the original projected polynomial target. -/
public structure RealProjectedQSVTRealization {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (L : Nat) (target : HilbertOperator (Qubits N)) where
  /-- Actual default-native circuit under the explicit projected-source access contract. -/
  circuit : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model N)
    (ProjectorPhase.layout N)
  /-- Exact source polynomial block of this very circuit. -/
  block_eq : projectedPhasePlusBlock (projectedOutputProjector left right L) right
    (circuit.binaryMatrix (ProjectedSignal.interpretation U left right)) = target
  /-- The independent query and rotation budget is met exactly. -/
  resources_exact : ProjectedEventProfile.HasExactCounts N L circuit.eventCost
  /-- The full sequential word retains source, projector and rotation dependencies. -/
  depth_exact : circuit.evaluatedEventDepth (fun _ => 1) = 4 * L

namespace RealProjectedQSVTRealization

/-- Resident systems are the full physical interface of the constructed circuit. -/
@[nolint unusedArguments]
public def liveSpace {N : Nat} {U : UnitaryOperator (Qubits N)}
    {left right : OrthogonalProjector N} {L : Nat} {target : HilbertOperator (Qubits N)}
    (_realization : RealProjectedQSVTRealization U left right L target) : SpacePool .quantum :=
  SpacePool.ofQuantumLayout (ProjectorPhase.layout N)

/-- One phase ancilla and the original N signal systems remain resident. -/
@[simp] public lemma liveSpace_logicalQubits {N : Nat}
    {U : UnitaryOperator (Qubits N)} {left right : OrthogonalProjector N}
    {L : Nat} {target : HilbertOperator (Qubits N)}
    (realization : RealProjectedQSVTRealization U left right L target) :
    SpacePool.count (.quantumSystems 2) realization.liveSpace = 1 + N := by
  change (QuantumLayout.uniform (1 + N) 2 Fin.val Fin.val_injective).dimensionCount 2 = _
  exact (QuantumLayout.dimensionCount_uniform (1 + N) 2 2 Fin.val Fin.val_injective).trans
    (if_pos rfl)

end RealProjectedQSVTRealization

/-- Construct the actual native realization from the original source hypotheses. -/
noncomputable def realProjectedQSVTOfMatchingParity {N L : Nat} {PRe : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (positive : 0 < L) :
    RealProjectedQSVTRealization U left right L
      (singularValuePolynomial right L (realPolynomialToComplex PRe)
        (projectedUnitaryBlock left right U)) := by
  let certificate :=
    ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses source
  let phases := projectedPhasesFromQSPCertificate
    certificate.certificate.φ₀ certificate.certificate.φs
  have length : phases.length = L := by
    exact (projectedPhasesFromQSPCertificate_length _ _).trans certificate.certificate.length_eq
  refine
    { circuit := Native.circuit (width := N) false phases
      block_eq := Native.circuit_of_real_certificate U left right false certificate positive
      resources_exact := ?_
      depth_exact := ?_ }
  · change _ = projectedEventBudget N L
    rw [Native.circuit_events, length]
    rfl
  · rw [Native.circuit_depth, length]

namespace Decomposition.Projected

/-- Original projected source theorem, with exact counts from the actual native circuit. -/
lemma sourceMain {N L : Nat} {PRe : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (positive : 0 < L) :
    ∃ realization : RealProjectedQSVTRealization U left right L
        (singularValuePolynomial right L (realPolynomialToComplex PRe)
          (projectedUnitaryBlock left right U)),
      ProjectedEventProfile.HasExactCounts N L realization.circuit.eventCost := by
  let realization := realProjectedQSVTOfMatchingParity U left right source positive
  exact ⟨realization, realization.resources_exact⟩

end Decomposition.Projected
end
end QuantumAlg.QSP.MultiQubit.QSVT
