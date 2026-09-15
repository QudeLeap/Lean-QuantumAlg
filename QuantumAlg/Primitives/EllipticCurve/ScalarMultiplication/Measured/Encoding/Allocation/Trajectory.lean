/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation.Correctness
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Initialization
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Trajectory

/-!
# Original scaled affine inputs establish the converted cascade domain

The supplied coordinates are canonical field words scaled by one fixed unit.
Their ordinary affine coordinates satisfy the existing mathematical trajectory.
Actual initialization supplies every internal work and selector condition, and
the inverse conversion recovers the complete ordinary initialized basis.

The density argument constrains only supported ket columns, retaining arbitrary
coherence and external references. The input predicate contains no execution,
prepared-work promise, or auxiliary register supplied by the caller.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute MeasuredPointAddition Allocation

/-- Original unit-scaled affine words follow the existing ordinary mathematical trajectory. -/
def convertedInputTrajectory {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (original : (before p.size count).register.Index) : Prop :=
  ∃ (exponent : (exponents p.size count).register.Index) (initial : AffinePoint E),
    original = inputLabel p.size count exponent
      (fieldWord ((coefficient : ZMod p) * initial.x))
      (fieldWord ((coefficient : ZMod p) * initial.y)) ∧
    inputTrajectory E points order
      (inputLabel p.size count exponent (fieldWord initial.x) (fieldWord initial.y))

private def convertedReadyTrajectory {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (prepared : (readyContext p.size count).register.Index) : Prop :=
  ∃ original, convertedInputTrajectory E points order coefficient original ∧
    prepared = initializedReadyBasis p count original

/-- Original affine support establishes every domain after actual inverse coordinate conversion. -/
theorem convertedInitializedSupport_of_input_trajectory {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {count : Nat}
    (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (input : DensityOperator (Register.prod (before p.size count).register Reference))
    (support : ∀ original, ¬convertedInputTrajectory E points order coefficient original.1 →
      input.matrix original original = 0) :
    convertedInitializedSupport E points order coefficient Reference input := by
  apply cascadeSupport_of_basisTrajectory
  refine MeasuredPointAddition.applyUnitary_support_of_kets
    ((initializedDensity p count Reference input).reindex
      (ContextPermutation.referenceBasis (body_entries p.size count) Reference).symm)
    (pairOperator p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference)
    (fun value => convertedReadyTrajectory E points order coefficient value.1)
    (fun value => basisTrajectory E points order value.1) ?_ ?_
  · intro value outside
    rw [DensityOperator.reindex_entry]
    apply initializedDensity_support p count Reference input
      (convertedInputTrajectory E points order coefficient)
      (convertedReadyTrajectory E points order coefficient)
      (fun original allowed => ⟨original, allowed, rfl⟩) support
    change ¬convertedReadyTrajectory E points order coefficient
      ((ContextPermutation.basis (body_entries p.size count)).symm
        (ContextPermutation.basis (body_entries p.size count) value.1))
    rw [Equiv.symm_apply_apply]
    exact outside
  · rintro ⟨basis, reference⟩ ⟨original, ⟨exponent, initial, rfl, trajectory⟩, rfl⟩
    refine ⟨(initializedReadyBasis p count
      (inputLabel p.size count exponent (fieldWord initial.x) (fieldWord initial.y)), reference),
      trajectory, ?_⟩
    have actual := pairOperator_initialized_fieldWords count coefficient⁻¹ exponent
      ((coefficient : ZMod p) * initial.x) ((coefficient : ZMod p) * initial.y) reference
    exact actual.trans (by rw [Units.inv_mul_cancel_left, Units.inv_mul_cancel_left])

/-- The actual converted circuit has the complete target on original scaled affine trajectories. -/
theorem convertedCircuit_density_of_input_trajectory {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {count : Nat}
    (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size count) Reference H)
    (support : ∀ input : (Register.prod (before p.size count).register Reference).Index,
      ¬convertedInputTrajectory E points order coefficient input.1 →
        original.quantumMarginal.matrix input input = 0) :
    ((convertedCircuit E points order coefficient).execute Reference original).quantumMarginal =
      convertedResultDensity E points order coefficient Reference original.quantumMarginal :=
  convertedCircuit_density E points order coefficient original
    (convertedInitializedSupport_of_input_trajectory E points order coefficient Reference
      original.quantumMarginal support)

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
