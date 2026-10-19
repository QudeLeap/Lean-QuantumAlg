/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.RecordState
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# The intrinsic reference family of the actual reduced-terminal reset

Every coefficient is the principal reference block of the actual reset
output. The classical coordinate change moves the existing service label
before the complete Store, incoming history and actual reset path. It never
identifies different records or removes a Store value.

The actual output is reconstructed exactly from these coefficients and its
actual local reset ket. This is a mathematical state identity, not a second
physical execution. Neither a clean-input premise nor branch normalization
is used. No old/new sampler equality or selected-success transfer is claimed.
The public-frame transport remains a separate construction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
namespace ReferenceFamily

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- A recordwise ket factor reconstructs the same complete joint reference state. -/
private lemma seededBlocks_of_record_factor {C : Type} [Fintype C]
    (ctx : RuntimeCtx .quantum) {Reference : Register}
    (source : ExecutionState C (ctx.register.prod Reference)) (label : ctx.register.Index)
    (factor : ∀ record : C, ∀ left right : ctx.register.Index,
      ∀ refLeft refRight : Reference.Index,
      (source.block record).matrix (left, refLeft) (right, refRight) =
        NormalizedVector.ket label left *
          (source.block record).matrix (label, refLeft) (label, refRight) *
            star (NormalizedVector.ket label right)) :
    source = ReferenceRecords.seededBlocks ctx label
      (ReferenceRecords.referenceSlices source label) := by
  apply ExecutionState.ext
  intro record
  apply DensityOperator.ext
  ext ⟨left, refLeft⟩ ⟨right, refRight⟩
  rw [ReferenceRecords.seededBlocks_entry, ReferenceRecords.referenceSlices_entry]
  exact (factor record left right refLeft refRight).trans
    (BasisSeeded.ket_factor label left right
      ((source.block record).matrix (label, refLeft) (label, refRight)))

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

/-- The entire output Store and original history/path remain mathematical history. -/
abbrev CoefficientHistory (History : Type) :=
  Store (Recovery.Layout.terminal p.size m) ×
    (History × (newReset E fieldTail m seed).Path)

/-- Reassociate complete actual records, retaining even zero-probability records. -/
def recordCoordinates (History : Type) :
    ResetRecord E fieldTail m seed History ≃
      (ClassicalOracleModel.empty.HiddenState ×
        CoefficientHistory E fieldTail m seed History) where
  toFun record := (record.2.1, (record.1, record.2.2))
  invFun record := (record.2.1, (record.1, record.2.2))
  left_inv record := by
    rcases record with ⟨stored, hidden, history, path⟩
    rfl
  right_inv record := by
    rcases record with ⟨hidden, stored, history, path⟩
    rfl

variable {Reference : Register} {History : Type} [Fintype History]

/-- Certified positive reference coefficients come from the actual complete reset output. -/
def coefficients
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ExecutionState (ClassicalOracleModel.empty.HiddenState ×
      CoefficientHistory E fieldTail m seed History) Reference :=
  (ReferenceRecords.referenceSlices
    ((newReset E fieldTail m seed).execute environment Reference state)
    (newResetLabel E fieldTail m seed)).mapClassical
      (recordCoordinates E fieldTail m seed History)

/-- Both external-reference coordinates agree with the same actual complete output record. -/
lemma coefficients_entry
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : ClassicalOracleModel.empty.HiddenState ×
      CoefficientHistory E fieldTail m seed History) (left right : Reference.Index) :
    ((coefficients (environment := environment) E fieldTail m seed state).block record).matrix
      left right =
      (newResetReferenceCoefficient (environment := environment) E fieldTail m seed state
        ((recordCoordinates E fieldTail m seed History).symm record)).matrix left right := by
  unfold coefficients
  rw [ExecutionState.coordinate_mapClassical_block]
  rfl

/-- The full coefficient family has exactly the arbitrary incoming subnormalized mass. -/
lemma coefficients_mass
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (coefficients (environment := environment) E fieldTail m seed state).mass = state.mass := by
  rw [coefficients, ExecutionState.mapClassical_mass]
  exact (ReferenceRecords.referenceSlices_mass_of_factor
    ((newReset E fieldTail m seed).execute environment Reference state)
    (newResetLabel E fieldTail m seed)
    (newReset_block_factor E fieldTail m seed state)).trans
      (Circuit.execute_mass (environment := environment) (newReset E fieldTail m seed) Reference
        state)

/-- Reversing the classical coordinates returns the exact original reference slices. -/
lemma coefficients_inverse
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (coefficients (environment := environment) E fieldTail m seed state).mapClassical
        (recordCoordinates E fieldTail m seed History).symm =
      ReferenceRecords.referenceSlices
        ((newReset E fieldTail m seed).execute environment Reference state)
        (newResetLabel E fieldTail m seed) :=
  ExecutionState.coordinate_mapClassical_inverse _
    (recordCoordinates E fieldTail m seed History)

/-- The actual reset output equals its intrinsic full-record reference family tensor its ket. -/
lemma actual_reset_eq_seededBlocks
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (newReset E fieldTail m seed).execute environment Reference state =
      ReferenceRecords.seededBlocks (Recovery.Layout.terminal p.size m)
        (newResetLabel E fieldTail m seed)
        (ReferenceRecords.referenceSlices
          ((newReset E fieldTail m seed).execute environment Reference state)
          (newResetLabel E fieldTail m seed)) := by
  exact seededBlocks_of_record_factor (Recovery.Layout.terminal p.size m)
    ((newReset E fieldTail m seed).execute environment Reference state) (newResetLabel E fieldTail
      m seed)
    (newReset_block_factor E fieldTail m seed state)

/-- The reassociated family reconstructs every actual Store/history and joint reference entry. -/
lemma actual_reset_eq_reconstructed
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (newReset E fieldTail m seed).execute environment Reference state =
      ReferenceRecords.seededBlocks (Recovery.Layout.terminal p.size m)
        (newResetLabel E fieldTail m seed)
        ((coefficients (environment := environment) E fieldTail m seed state).mapClassical
          (recordCoordinates E fieldTail m seed History).symm) := by
  rw [coefficients_inverse]
  exact actual_reset_eq_seededBlocks E fieldTail m seed state

end

end ReferenceFamily
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
