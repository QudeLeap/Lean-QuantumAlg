/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Output.Bank.Density

/-!
# Exact probability mass of the streaming output bank density

The existing zero-private-column inclusion is isometric. Consequently, the
positive bank matrix at a complete final Store and original-History predicate
has exactly the mass of the same actual selected quantum output. Its trace is
bounded by the arbitrary incoming subnormalized mass, without normalization.

These are streaming-side identities, not old/new instrument or success
theorems.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace OutputBankTrace

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord
open Recovery.Stage.PointCoordinates.StageWord.PathWord
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
open OutputBankDensity
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma initializedColumns_gram (width m : Nat) (Reference : Register) :
    (initializedColumns width m Reference).conjTranspose *
        initializedColumns width m Reference = 1 := by
  have injective : Function.Injective (initializedBasis width m Reference) := by
    intro first second same
    have coordinates := congrArg (joint width m Reference) same
    simpa only [initializedBasis, Equiv.apply_symm_apply, Prod.mk.injEq, true_and]
      using coordinates
  ext row column
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, initializedColumns,
    apply_ite (fun value : ℂ => star value), star_one, star_zero, ite_mul,
    one_mul, zero_mul, Fintype.sum_ite_eq', injective.eq_iff, Matrix.one_apply]

private lemma initialized_sandwich_trace (width m : Nat) (Reference : Register)
    (density : Matrix (Bank width m Reference) (Bank width m Reference) ℂ) :
    (initializedColumns width m Reference * density *
      (initializedColumns width m Reference).conjTranspose).trace = density.trace := by
  rw [Matrix.trace_mul_cycle, initializedColumns_gram, Matrix.one_mul]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

variable {Reference : Register} {History : Type} [Fintype History]

/-- The bank trace retains exactly the mass of this complete actual output fiber. -/
lemma actual_reset_fourier_outputBankDensity_mass (r : Nat)
    (points : Fin (2 * m) → AffinePoint E)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (((stages E r points (Recovery.Layout.order m)).execute environment Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
        state)).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.mass
        =
      (outputBankDensity (environment := environment) E fieldTail m seed r points state predicate
        final).trace.re := by
  unfold DensityOperator.mass
  rw [actual_reset_fourier_outputBankDensity E fieldTail m seed r points state predicate
    positive fits final, initialized_sandwich_trace]

/-- The same positive bank matrix is subnormalized by the actual arbitrary incoming mass. -/
lemma outputBankDensity_trace_le_input (r : Nat)
    (points : Fin (2 * m) → AffinePoint E)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (outputBankDensity (environment := environment) E fieldTail m seed r points state predicate
      final).trace.re ≤
      state.mass := by
  rw [← actual_reset_fourier_outputBankDensity_mass E fieldTail m seed r points state
    predicate positive fits final, ExecutionState.quantumMarginal_mass]
  exact (ExecutionState.filterClassical_mass_le
    ((stages E r points (Recovery.Layout.order m)).execute environment Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference state))
    (fun record => record.1 = final ∧ predicate record.2.2.1.1)).trans_eq
      ((Circuit.execute_mass (environment := environment) (stages E r points (Recovery.Layout.order
        m)) Reference
        ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
          state)).trans
          (Circuit.execute_mass (environment := environment) (Recovery.Initialization.newReset E
            fieldTail m seed)
            Reference state))

end

end OutputBankTrace
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
