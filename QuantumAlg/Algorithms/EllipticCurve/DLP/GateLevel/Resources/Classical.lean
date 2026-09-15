/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Resources.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.ResourceProjections.Unitary

/-!
# Classical-operation absence in the original literal ECDLP unitary

The source preparation, group-action query and pair of inverse Fourier
transforms contain no classical-operation event. These are pure unitary
resource facts; the actual measured circuit charges its classical recovery
separately.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelResources

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem classicalOperationEvent_not_elementary
    (label : Resource.ClassicalOpLabel) :
    ¬ UniformSuperposition.elementaryEvent
      (.classicalOperation label : Resource.Event .quantum) := by
  intro elementary
  simp only [UniformSuperposition.elementaryEvent,
    UniformSuperposition.hadamardEvent_eq_gate,
    UniformSuperposition.xEvent_eq_gate,
    UniformSuperposition.rotationYEvent_eq_gate,
    UniformSuperposition.cnotEvent_eq_gate] at elementary
  rcases elementary with equality | equality | equality | equality <;>
    cases equality

/-- The literal order preparation has no classical-operation leaf. -/
theorem paddedPreparation_classicalOperationCard_zero
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) :
    FiniteCyclicDLP.Canonical.classicalOperationCard
        (B.paddedPreparation (problem I)).eventCost = 0 := by
  unfold FiniteCyclicDLP.Canonical.classicalOperationCard
  rw [Multiset.countP_eq_zero]
  intro event member
  cases event with
  | classicalOperation label =>
      exfalso
      have countZero := B.paddedPreparation_count_zero_of_not_elementary
        (problem I) (.classicalOperation label)
          (classicalOperationEvent_not_elementary label)
      exact (Multiset.count_eq_zero.mp countZero) member
  | classicalSubroutine _ =>
      simp [FiniteCyclicDLP.Canonical.isClassicalOperation]
  | gate _ =>
      simp [FiniteCyclicDLP.Canonical.isClassicalOperation]
  | preparation _ =>
      simp [FiniteCyclicDLP.Canonical.isClassicalOperation]
  | measurement _ =>
      simp [FiniteCyclicDLP.Canonical.isClassicalOperation]
  | quantumSubroutine _ =>
      simp [FiniteCyclicDLP.Canonical.isClassicalOperation]

/-- The preparation-query-readout circuit contains no classical operation;
all deterministic classical work remains in the typed recovery tail. -/
theorem quantumCircuit_classicalOperationCard_zero
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (A : Access I) :
    FiniteCyclicDLP.Canonical.classicalOperationCard
        (GateLevelAttempt.quantumCircuit I B A).eventCost = 0 := by
  have queryZero : FiniteCyclicDLP.Canonical.classicalOperationCard
      (ResourcePool.singleton (uPQEvent I)) = 0 := by
    exact FiniteCyclicDLP.Canonical.classicalOperationCard_singleton_nonClassical
      (uPQEvent I) (by
        intro label equality
        cases equality) 1
  rw [quantumCircuit_eventCost,
    FiniteCyclicDLP.Canonical.classicalOperationCard_add,
    FiniteCyclicDLP.Canonical.classicalOperationCard_add,
    FiniteCyclicDLP.Canonical.classicalOperationCard_add,
    paddedPreparation_classicalOperationCard_zero,
    queryZero,
    Resources.Classical.inverseQFTCircuit_classicalOperationCard_zero]

end

end GateLevelResources
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
