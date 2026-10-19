/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.History.Columns
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.InitializedFourier
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.History.Matrices
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.History.Paths
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Terminal.HistorySelection

/-!
# Actual converted Fourier densities at every original History predicate

The two actual pair conversions preserve every selected original-history
fiber. The existing stage law and literal sequential Path reassociation then
move that selection to the same actual input. Applying the existing converted
Fourier law to the selected actual reset output discharges its initialization
premise using the intrinsic density of that same selected state.

Complete Stores, arbitrary external Reference, dirty input histories, reset
and converted execution Paths remain present. No zero contribution is removed,
and all four original conversion factors keep their existing order. No caller
initialization certificate, common output density, complete instrument equality
or success claim is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace HistoryDensity

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion (storeDensity)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths (initializedColumns)
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The Boolean observation selects exactly the same complete density blocks as the predicate. -/
private lemma filterHistory_eq_selectHistory {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (predicate : History → Prop) :
    state.filterClassical (fun record => predicate record.2) =
      state.selectHistory (fun history => decide (predicate history)) true := by
  apply ExecutionState.ext
  intro record
  simp only [State.selectHistory, ExecutionState.selectClassical_block,
    ExecutionState.filterClassical_block, decide_eq_true_eq]

/-- Intersect the original history selection with one complete final Store. -/
private lemma selected_store_density {width m : Nat} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Recovery.Layout.terminal width m)) (predicate : History → Prop) :
    storeDensity (state.filterClassical (fun record => predicate record.2.2)) stored =
      (state.filterClassical (fun record => record.1 = stored ∧ predicate
        record.2.2)).quantumMarginal.matrix
        := by
  unfold storeDensity
  apply congrArg (fun selected : State (Recovery.Layout.terminal width m) Reference
    (ClassicalOracleModel.empty.HiddenState × History) => selected.quantumMarginal.matrix)
  apply ExecutionState.ext
  intro record
  by_cases atStore : record.1 = stored <;> by_cases keep : predicate record.2.2 <;>
    simp only [ExecutionState.filterClassical_block, atStore, keep,
      true_and, false_and, and_false, if_true, if_false]

/-- Both literal conversion instructions carry the original History selection through unchanged. -/
private lemma pair_execute_filter_history (width m : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (predicate : History → Prop) :
    ((pairCircuit width m modulus coefficient).execute environment Reference state).filterClassical
        (fun record => predicate record.2.2.1) =
      (pairCircuit width m modulus coefficient).execute environment Reference
        (state.filterClassical (fun record => predicate record.2.2)) := by
  have supported : (pairCircuit width m modulus coefficient).IsLocal := by
    change True ∧ True
    exact ⟨True.intro, True.intro⟩
  have outputSelection := filterHistory_eq_selectHistory
    ((pairCircuit width m modulus coefficient).execute environment Reference state)
    (fun history => predicate history.2.1)
  have inputSelection := filterHistory_eq_selectHistory state
    (fun history => predicate history.2)
  exact outputSelection.trans
    ((Recovery.Reference.Terminal.execute_selectHistory (environment := environment)
      (pairCircuit width m modulus
      coefficient) supported
      Reference state (fun history => decide (predicate history)) true).trans
      (congrArg (fun selected =>
        (pairCircuit width m modulus coefficient).execute environment Reference selected)
          inputSelection.symm))

/-- Conversion acts on the same full Store and arbitrary original-history matrix fiber. -/
private lemma pair_history_store_density (width m : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : (ZMod modulus.val)ˣ)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Recovery.Layout.terminal width m)) (predicate : History → Prop) :
    (((pairCircuit width m modulus coefficient).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      pairOperator (environment := environment) width m modulus coefficient Reference *
        storeDensity (state.filterClassical (fun record => predicate record.2.2)) stored *
        (pairOperator (environment := environment) width m modulus coefficient
          Reference).conjTranspose := by
  calc
    _ = storeDensity
        (((pairCircuit width m modulus coefficient).execute environment Reference
          state).filterClassical
          (fun record => predicate record.2.2.1)) stored :=
      (selected_store_density
        ((pairCircuit width m modulus coefficient).execute environment Reference state) stored
        (fun history => predicate history.1)).symm
    _ = storeDensity ((pairCircuit width m modulus coefficient).execute environment Reference
        (state.filterClassical (fun record => predicate record.2.2))) stored :=
      congrArg (fun selected => storeDensity selected stored)
        (pair_execute_filter_history width m modulus coefficient Reference state predicate)
    _ = _ := pair_store_density width m modulus coefficient Reference
      (state.filterClassical (fun record => predicate record.2.2)) stored

/-- The actual four-conversion wrapper keeps an arbitrary original History predicate exactly. -/
lemma converted_history_filter_input {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Recovery.Layout.terminal p.size m)) (predicate : History → Prop) :
    (((convertedStages E r points (Recovery.Layout.order m) coefficient).execute environment
      Reference state).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      storeDensity ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute
        environment Reference (state.filterClassical (fun record => predicate record.2.2))) final
        := by
  let modulus := MeasuredUncompute.InPlaceTarget.modulusWord p
  let inverse := pairCircuit p.size m modulus coefficient⁻¹
  let forward := pairCircuit p.size m modulus coefficient
  let body := Recovery.Stage.stages E r points (Recovery.Layout.order m)
  let operator := pairOperator (environment := environment) p.size m modulus coefficient Reference
  have outer := HistoryMatrices.seq_store_history_matrix (environment := environment) inverse
    (body.seq forward)
    state final predicate
  have inner := HistoryMatrices.seq_store_history_matrix (environment := environment) body forward
    (inverse.execute environment Reference state) final (fun history => predicate history.1)
  change (((convertedStages E r points (Recovery.Layout.order m) coefficient).execute environment
    Reference state).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      (((body.seq forward).execute environment Reference (inverse.execute environment Reference
        state)).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.matrix
      at outer
  have selected := HistoryPaths.actual_trace_history_filter_input (environment := environment) (m
    := m) E r points Reference
    (2 * m) id
    (History := History × inverse.Path) (inverse.execute environment Reference state) final
    (fun history => predicate history.1)
  have inverseSelected := pair_execute_filter_history (environment := environment) p.size m
    modulus coefficient⁻¹ Reference
    state predicate
  have movedInput := congrArg
    (fun selected =>
      storeDensity (width := p.size) (m := m) (Reference := Reference)
        (body.execute environment Reference selected) final) inverseSelected
  have bodySelected :=
    (selected_store_density (body.execute environment Reference (inverse.execute environment
      Reference state)) final
      (fun history => predicate history.1.1)).trans (selected.trans movedInput)
  have outerFiltered := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal inverse (body.seq forward) environment
      (state.filterClassical (fun record => predicate record.2.2)) final)
  have innerFiltered := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal body forward environment
      (inverse.execute environment Reference (state.filterClassical (fun record => predicate
        record.2.2)))
      final)
  change storeDensity ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute
    environment Reference (state.filterClassical (fun record => predicate record.2.2))) final =
    storeDensity ((body.seq forward).execute environment Reference
      (inverse.execute environment Reference (state.filterClassical (fun record => predicate
        record.2.2))))
      final at outerFiltered
  change storeDensity ((body.seq forward).execute environment Reference
      (inverse.execute environment Reference (state.filterClassical (fun record => predicate
        record.2.2))))
      final =
    storeDensity (forward.execute environment Reference (body.execute environment Reference
      (inverse.execute environment Reference (state.filterClassical (fun record => predicate
        record.2.2)))))
      final at innerFiltered
  dsimp only [forward] at innerFiltered
  have forwardFiltered := pair_store_density (environment := environment) p.size m modulus
    coefficient Reference
    (body.execute environment Reference
      (inverse.execute environment Reference (state.filterClassical (fun record => predicate
        record.2.2))))
    final
  have filtered := outerFiltered.trans (innerFiltered.trans forwardFiltered)
  change storeDensity ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute
    environment Reference (state.filterClassical (fun record => predicate record.2.2))) final =
    operator *
      storeDensity (body.execute environment Reference
        (inverse.execute environment Reference (state.filterClassical (fun record => predicate
          record.2.2))))
        final * (operator).conjTranspose
      at filtered
  calc
    _ = (((forward.execute environment Reference (body.execute environment Reference
        (inverse.execute environment Reference state)))).filterClassical
          (fun record => record.1 = final ∧ predicate record.2.2.1.1.1)).quantumMarginal.matrix
        := outer.trans inner
    _ = operator *
        storeDensity ((body.execute environment Reference (inverse.execute environment Reference
          state)).filterClassical
          (fun record => predicate record.2.2.1.1)) final *
        (operator).conjTranspose :=
      pair_history_store_density p.size m modulus coefficient Reference
        (body.execute environment Reference (inverse.execute environment Reference state)) final
        (fun history => predicate history.1.1)
    _ = operator *
        storeDensity (body.execute environment Reference
          (inverse.execute environment Reference (state.filterClassical (fun record => predicate
            record.2.2))))
          final * (operator).conjTranspose :=
      congrArg (fun density => operator * density *
        (operator).conjTranspose) bodySelected
    _ = _ := filtered.symm

/-- The same actual reset input gives the converted Fourier CP sum at every original History.

The final selector reads the original incoming History, separately from the
actual reset Path and the complete convertedStages Path. The sampler bounds
are precisely the existing positive interval size and finite-width bound.
-/
lemma actual_reset_converted_fourier_history_density {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (fieldTail m : Nat) (seed : AffinePoint E)
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    (((convertedStages E r points (Recovery.Layout.order m) coefficient).execute environment
      Reference
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
        state)).filterClassical
        (fun record => record.1 = final ∧ predicate record.2.2.1.1)).quantumMarginal.matrix =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (convertedFourierBankWord (environment := environment) E r points coefficient
                Reference path *
                Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment :=
                  environment)
                  E fieldTail m seed state predicate original *
                (convertedFourierBankWord (environment := environment) E r points coefficient
                  Reference path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0 := by
  have selected :=
    converted_history_filter_input (environment := environment) E r points coefficient Reference
      (History := History × (Recovery.Initialization.newReset E fieldTail m seed).Path)
      ((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference state)
      final (fun history => predicate history.1)
  refine selected.trans ?_
  exact actual_initialized_converted_fourier_store_density (m := m) E r points coefficient Reference
    (((Recovery.Initialization.newReset E fieldTail m seed).execute environment Reference
      state).filterClassical
      (fun record => predicate record.2.2.1))
    (Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment := environment)
      E fieldTail m seed state predicate)
    (Recovery.Initialization.HistoryColumns.newReset_history_store_initialized
      E fieldTail m seed state predicate) positive fits final

end

end HistoryDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
