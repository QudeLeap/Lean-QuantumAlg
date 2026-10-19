/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.InitializedColumns
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.History.Paths
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.TwoBankFourier

/-!
# Initialized Fourier densities of each actual original-history fiber

The actual reset support is proved again for each complete record after
selecting an arbitrary predicate of the original History. The bank density
is a principal submatrix of that same selected actual output, with its full
Store, reset Path and external Reference still present. Aggregate support of
an unselected Store density is never used as support of the selected state.

The actual full stream then has its existing Fourier CP sum at that original history
predicate. All dirty input, zero-mass records and exponent width zero remain included.
This bridge does not prove a common output sigma, old/new instrument equality,
initialization of a public frame or an Algorithm resource bound.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
namespace HistoryColumns

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open Recovery.Stage (stages)
open Recovery.Stage.PointCoordinates (Bank)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
  (joint initializedBasis initializedColumns fourierBankWord)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
  (actual_initialized_fourier_store_density)
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion (storeDensity)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open scoped BigOperators ComplexOrder

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail m : Nat) (seed : AffinePoint E)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Selection keeps or zeros one complete actual reset record, with the same seed support. -/
private lemma newReset_history_block_factor
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (record : ResetRecord E fieldTail m seed History)
    (left right : (Recovery.Layout.terminal p.size m).register.Index)
    (refLeft refRight : Reference.Index) :
    ((((newReset E fieldTail m seed).execute environment Reference state).filterClassical
      (fun value => predicate value.2.2.1)).block record).matrix
        (left, refLeft) (right, refRight) =
      NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) left *
        ((((newReset E fieldTail m seed).execute environment Reference state).filterClassical
          (fun value => predicate value.2.2.1)).block record).matrix
          (newResetLabel E fieldTail m seed, refLeft)
          (newResetLabel E fieldTail m seed, refRight) *
        star (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (newResetLabel E fieldTail m seed) right) := by
  by_cases selected : predicate record.2.2.1
  · simpa only [ExecutionState.filterClassical_block, if_pos selected] using
      newReset_block_factor E fieldTail m seed state record left right refLeft refRight
  · simp only [ExecutionState.filterClassical_block, if_neg selected,
      DensityOperator.zero_matrix, Matrix.zero_apply, mul_zero, zero_mul]

/-- The selected Store fiber is supported by the actual reset label, record by record. -/
private lemma actual_history_store_seeded
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (predicate : History → Prop) :
    BasisSeeded.Holds (newResetLabel E fieldTail m seed)
      (((newReset E fieldTail m seed).execute environment Reference state).filterClassical
        (fun record => predicate record.2.2.1)) := by
  let selected : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × (newReset E fieldTail m seed).Path)) :=
    ((newReset E fieldTail m seed).execute environment Reference state).filterClassical
      (fun record => predicate record.2.2.1)
  apply BasisSeeded.of_entries (ctx := Recovery.Layout.terminal p.size m)
    (Reference := Reference) (newResetLabel E fieldTail m seed) selected
    (fun stored left right =>
      ∑ history : ClassicalOracleModel.empty.HiddenState ×
          (History × (newReset E fieldTail m seed).Path),
        (selected.block (stored, history)).matrix
          (newResetLabel E fieldTail m seed, left)
          (newResetLabel E fieldTail m seed, right))
  intro stored left right leftRef rightRef
  change storeDensity selected stored (left, leftRef) (right, rightRef) = _
  rw [InitializedOutput.storeDensity_history_sum (width := p.size) (m := m)
    Reference selected stored]
  simp only [Matrix.sum_apply]
  calc
    _ = ∑ history : ClassicalOracleModel.empty.HiddenState ×
          (History × (newReset E fieldTail m seed).Path),
        NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
            (newResetLabel E fieldTail m seed) left *
          (selected.block (stored, history)).matrix
            (newResetLabel E fieldTail m seed, leftRef)
            (newResetLabel E fieldTail m seed, rightRef) *
          star (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
            (newResetLabel E fieldTail m seed) right) :=
      Finset.sum_congr rfl (fun history _ =>
        newReset_history_block_factor E fieldTail m seed state predicate (stored, history)
          left right leftRef rightRef)
    _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]

/-- Extract the bank matrix from this same selected actual complete Store fiber. -/
def actualHistoryBankDensity
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  (storeDensity (((newReset E fieldTail m seed).execute environment Reference state).filterClassical
    (fun record => predicate record.2.2.1)) stored).submatrix
      (initializedBasis p.size m Reference) (initializedBasis p.size m Reference)

/-- The intrinsic selected bank matrix is positive semidefinite even at zero mass. -/
lemma actualHistoryBankDensity_positive (E : PrimeFieldShortWeierstrass p)
    (fieldTail m : Nat) (seed : AffinePoint E)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    (actualHistoryBankDensity (environment := environment) E fieldTail m seed state predicate
      stored).PosSemidef :=
  (((((newReset E fieldTail m seed).execute environment Reference state).filterClassical
    (fun record => predicate record.2.2.1)).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.positive).submatrix
        (initializedBasis p.size m Reference)

section InitializedHistoryStore

attribute [local irreducible] newReset joint

/-- Every selected actual Store fiber has its own unconditional initialized-column form. -/
lemma newReset_history_store_initialized
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity (((newReset E fieldTail m seed).execute environment Reference
      state).filterClassical
        (fun record => predicate record.2.2.1)) stored =
      initializedColumns p.size m Reference *
        actualHistoryBankDensity (environment := environment) E fieldTail m seed state predicate
          stored *
        (initializedColumns p.size m Reference).conjTranspose := by
  let coordinates := (joint p.size m Reference).trans
    (Equiv.prodAssoc (Fin 2) Bool (Bank p.size m Reference)).symm
  apply InitializedOutput.seeded_selected_sandwich
    (Local := (Recovery.Layout.terminal p.size m).register.Index) (Frame := Reference.Index)
    (Selector := Fin 2 × Bool) (BankIndex := Bank p.size m Reference)
    (localDecision := (Recovery.Layout.terminal p.size m).register.decEq)
    coordinates (initializedBasis p.size m Reference) (initializedColumns p.size m Reference)
    (storeDensity (((newReset E fieldTail m seed).execute environment Reference
      state).filterClassical
      (fun record => predicate record.2.2.1)) stored)
    (newResetLabel E fieldTail m seed) (0, false) (fun _ => rfl)
    (actual_history_store_seeded E fieldTail m seed state predicate stored)
  · intro selector bank outside
    apply InitializedOutput.uninitialized_not_resetLabel E fieldTail m seed
      selector.1 selector.2 bank
    intro same
    exact outside (Prod.ext same.1 same.2)
  · intro density rowSelector columnSelector rowBank columnBank
    rcases rowSelector with ⟨control, memory⟩
    rcases columnSelector with ⟨columnControl, columnMemory⟩
    change (initializedColumns p.size m Reference * density *
        (initializedColumns p.size m Reference).conjTranspose)
        ((joint p.size m Reference).symm (control, (memory, rowBank)))
        ((joint p.size m Reference).symm (columnControl, (columnMemory, columnBank))) =
      if (control, memory) = ((0 : Fin 2), false) then
        (if (columnControl, columnMemory) = ((0 : Fin 2), false) then
          density rowBank columnBank else 0) else 0
    simpa only [Prod.mk.injEq] using
      InitializedOutput.initialized_sandwich_entry (width := p.size) (m := m) Reference density
        control columnControl memory columnMemory rowBank columnBank

end InitializedHistoryStore

/-- The actual full stream has its Fourier CP sum at every original History predicate.

The predicate selects the original incoming History while the actual reset
Path and generated stage Path remain separate coordinates. The only sampler
bounds are the existing positive interval size and finite-width upper bound.
-/
lemma actual_reset_fourier_history_density (r : Nat)
    (points : Fin (2 * m) → AffinePoint E)
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (((stages (m := m) E r points (Recovery.Layout.order m)).execute environment Reference
      ((newReset E fieldTail m seed).execute environment Reference state)).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.matrix =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (fourierBankWord (environment := environment) (m := m) E r points Reference path *
                actualHistoryBankDensity (environment := environment) E fieldTail m seed state
                  predicate original *
                (fourierBankWord (environment := environment) (m := m) E r points Reference
                  path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0 := by
  have selected :
      (((stages (m := m) E r points (Recovery.Layout.order m)).execute environment Reference
        ((newReset E fieldTail m seed).execute environment Reference state)).filterClassical
          (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.matrix =
        storeDensity ((stages (m := m) E r points (Recovery.Layout.order m)).execute environment
          Reference
          (((newReset E fieldTail m seed).execute environment Reference state).filterClassical
            (fun record => predicate record.2.2.1))) final := by
    exact HistoryPaths.actual_trace_history_filter_input (m := m)
      E r points Reference (2 * m) id
      (History := History × (newReset E fieldTail m seed).Path)
      ((newReset E fieldTail m seed).execute environment Reference state) final
      (fun history => predicate history.1)
  refine selected.trans ?_
  exact actual_initialized_fourier_store_density (m := m) E r points Reference
    (((newReset E fieldTail m seed).execute environment Reference state).filterClassical
      (fun record => predicate record.2.2.1))
    (actualHistoryBankDensity (environment := environment) E fieldTail m seed state predicate)
    (newReset_history_store_initialized E fieldTail m seed state predicate) positive fits final

end

end HistoryColumns
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Initialization
