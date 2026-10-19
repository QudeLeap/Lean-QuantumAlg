/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Correctness
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Target
import all QuantumAlg.Core.Execution.Reindex.Permutation

/-!
# Mathematical basis trajectories establish coherent cascade support

The trajectory follows the independent complete point permutations and checks
the original point domain before each step. Exact ket action carries the full
density, including all off-diagonal and external-reference entries. Thus the
trajectory support condition applies to coherent inputs, not just mixtures
of separately tested computational-basis states.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

/-- The prescribed mathematical trajectory checks the original domain before each point action. -/
def basisTrajectory {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) :
    List (Fin count) → (readyContext p.size count).register.Index → Prop
  | [], _ => True
  | active :: remaining, value =>
      stepAdmissible E (points active) active value ∧
        basisTrajectory E points remaining (stepPermutation E (points active) active value)

/-- The full independent step density follows its exact complete-basis permutation. -/
lemma stepTarget_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register)
    (density : DensityOperator (Register.prod (readyContext p.size count).register Reference)) :
    DensityOperator.applyUnitary (stepTarget E Q active Reference) density =
      density.reindex (S := Register.prod (readyContext p.size count).register Reference)
        (Equiv.prodCongr (stepPermutation E Q active) (Equiv.refl Reference.Index)) :=
  DensityOperator.applyUnitary_eq_reindex_of_kets density (stepTarget E Q active Reference)
    (Equiv.prodCongr (stepPermutation E Q active) (Equiv.refl Reference.Index))
    (fun input => stepTarget_apply_ket E Q active input.1 input.2)

/-- Original mathematical basis trajectories establish every intermediate full-density domain. -/
lemma cascadeSupport_of_basisTrajectory {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (Reference : Register)
    (density : DensityOperator (Register.prod (readyContext p.size count).register Reference))
    (support : ∀ input, ¬basisTrajectory E points order input.1 →
      density.matrix input input = 0) :
    cascadeSupport E points Reference order density := by
  induction order generalizing density with
  | nil => trivial
  | cons active remaining ih =>
      refine ⟨?_, ih _ ?_⟩
      · intro input outside
        exact support input (fun allowed => outside allowed.1)
      · exact DensityOperator.applyUnitary_support_of_kets density
          (stepTarget E (points active) active Reference)
          (Equiv.prodCongr (stepPermutation E (points active) active) (Equiv.refl Reference.Index))
          (fun input => stepTarget_apply_ket E (points active) active input.1 input.2)
          (fun input => basisTrajectory E points (active :: remaining) input.1)
          (fun output => basisTrajectory E points remaining output.1)
          (fun _ allowed => allowed.2) support

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
