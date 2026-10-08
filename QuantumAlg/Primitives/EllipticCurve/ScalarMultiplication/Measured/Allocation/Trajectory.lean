/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Correctness
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Trajectory

/-!
# Full initialized scalar correctness from original-input trajectories

The input predicate follows the independent point permutations starting from
the fixed basis established by actual allocation. It asks the caller for no
auxiliary register, initialized cell or prepared work premise. The resulting
state theorem covers the complete circuit and arbitrary coherent reference
extensions on this mathematical trajectory domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution

/-- Original supplied coordinates follow the prescribed mathematical point trajectory. -/
def inputTrajectory {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (original : (before p.size count).register.Index) : Prop :=
  basisTrajectory E points order (initializedReadyBasis p count original)

/-- Original-input trajectory support establishes the independently initialized cascade domain. -/
theorem initialized_cascadeSupport {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (Reference : Register)
    (input : DensityOperator (Register.prod (before p.size count).register Reference))
    (support : ∀ original, ¬inputTrajectory E points order original.1 →
      input.matrix original original = 0) :
    cascadeSupport E points Reference order
      ((initializedDensity p count Reference input).reindex
        (ContextPermutation.referenceBasis (body_entries p.size count) Reference).symm) := by
  apply cascadeSupport_of_basisTrajectory
  intro value outside
  rw [DensityOperator.reindex_entry]
  apply initializedDensity_support p count Reference input
    (inputTrajectory E points order) (basisTrajectory E points order)
    (fun _ allowed => allowed) support
  change ¬basisTrajectory E points order
    ((ContextPermutation.basis (body_entries p.size count)).symm
      (ContextPermutation.basis (body_entries p.size count) value.1))
  rw [Equiv.symm_apply_apply]
  exact outside

/-- The same complete actual circuit realizes the full target from its original input domain. -/
theorem circuit_density_of_input_trajectory {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (before p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : ∀ input : (Register.prod (before p.size count).register Reference).Index,
      ¬inputTrajectory E points order input.1 → original.quantumMarginal.matrix input input = 0) :
    ((circuit E points order).execute Reference original).quantumMarginal =
      resultDensity E points order Reference original.quantumMarginal :=
  circuit_density E points order original
    (initialized_cascadeSupport E points order Reference original.quantumMarginal support)

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
