/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.HistoryDensity
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Output.Bank.Trace

/-!
# Positive output bank densities of the actual converted Fourier stream

The same actual reset fibers determine every legal-path CP summand of the
literal converted protocol. Its inverse and forward pair conversions retain
all four factors in their original order. No normalization, clean input or
caller initialization certificate is introduced.

This proves the streaming side and its exact probability mass; comparison
with the old terminal instrument remains a separate theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace OutputBankDensity

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open Recovery.Stage.PointCoordinates (Bank)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths (initializedColumns)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open Recovery.Initialization.HistoryColumns
  (actualHistoryBankDensity actualHistoryBankDensity_positive)
open Recovery.Conversion.HistoryDensity (actual_reset_converted_fourier_history_density)
open scoped BigOperators ComplexOrder

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

variable {Reference : Register} {History : Type} [Fintype History]

/-- All legal measured paths contribute separately, including zero CP terms. -/
def outputBankDensity (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (final : Store (Recovery.Layout.terminal p.size m)) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  ∑ path : Fin (2 * m) → Branch p.size m,
    ∑ original : Store (Recovery.Layout.terminal p.size m),
      if traceValid p.size m (2 * m) id path original final then
        convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
          Reference path *
          actualHistoryBankDensity (environment := environment) E fieldTail m seed state predicate
            original *
          (convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
            Reference path).conjTranspose
      else 0

/-- Positivity follows from each actual selected input fiber, even when its mass is zero. -/
lemma outputBankDensity_positive (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (final : Store (Recovery.Layout.terminal p.size m)) :
    (outputBankDensity (environment := environment) E fieldTail m seed r points coefficient state
      predicate final).PosSemidef
        := by
  unfold outputBankDensity
  apply Matrix.posSemidef_sum
  intro path _
  apply Matrix.posSemidef_sum
  intro original _
  by_cases valid : traceValid p.size m (2 * m) id path original final
  · rw [if_pos valid]
    exact (actualHistoryBankDensity_positive E fieldTail m seed state predicate
      original).mul_mul_conjTranspose_same
      (convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
        Reference path)
  · rw [if_neg valid]
    exact Matrix.PosSemidef.zero

/-- The actual full Store/history fiber has the zero-private-column factor of this same density.

Every external Reference entry, complete Store and original-History predicate
is retained. The actual reset and stage Paths remain distinct coordinates.
-/
lemma actual_reset_converted_fourier_outputBankDensity (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (((convertedStages (m := m) E r points (Recovery.Layout.order m) coefficient).execute
      environment Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
        state)).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.matrix
        =
      initializedColumns p.size m Reference *
        outputBankDensity (environment := environment) E fieldTail m seed r points coefficient
          state predicate final *
        (initializedColumns p.size m Reference).conjTranspose := by
  rw [actual_reset_converted_fourier_history_density E fieldTail m seed r points coefficient
    state predicate positive fits final]
  unfold outputBankDensity
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro path _
  apply Finset.sum_congr rfl
  intro original _
  by_cases valid : traceValid p.size m (2 * m) id path original final
  · rw [if_pos valid, if_pos valid]
  · simp only [if_neg valid, Matrix.mul_zero, Matrix.zero_mul]

/-- The bank trace retains exactly the mass of this complete actual output fiber. -/
lemma actual_reset_converted_fourier_outputBankDensity_mass (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (((convertedStages (m := m) E r points (Recovery.Layout.order m) coefficient).execute
      environment Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
        state)).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.mass
        =
      (outputBankDensity (environment := environment) E fieldTail m seed r points coefficient
        state predicate final).trace.re
        := by
  unfold DensityOperator.mass
  rw [actual_reset_converted_fourier_outputBankDensity E fieldTail m seed r points coefficient
    state predicate positive fits final, OutputBankTrace.initialized_sandwich_trace]

/-- The same positive bank matrix is subnormalized by the actual arbitrary incoming mass. -/
lemma outputBankDensity_trace_le_input (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (outputBankDensity (environment := environment) E fieldTail m seed r points coefficient state
      predicate final).trace.re ≤
      state.mass := by
  rw [← actual_reset_converted_fourier_outputBankDensity_mass E fieldTail m seed r points
    coefficient state predicate positive fits final, ExecutionState.quantumMarginal_mass]
  exact (ExecutionState.filterClassical_mass_le
    ((convertedStages (m := m) E r points (Recovery.Layout.order m) coefficient).execute
      environment Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference state))
    (fun record => record.1 = final ∧ predicate record.2.2.1.1)).trans_eq
      ((Circuit.execute_mass (environment := environment) (convertedStages (m := m) E r points
        (Recovery.Layout.order m) coefficient) Reference
        ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
          state)).trans
          (Circuit.execute_mass (environment := environment) (Recovery.Initialization.newReset E
            fieldTail m seed)
            Reference state))

end

end OutputBankDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
