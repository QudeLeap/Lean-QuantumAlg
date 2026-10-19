/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reload
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Preparation.Coordinates
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Actual first allocation and literal loading establish the recycled-bank seed

This proves initialization of the same
Context.prepare program used by the first member. Arbitrary incoming
classical, hidden-history and external-reference correlations are admitted.
No normalization, external clean bank or caller seed certificate is needed.
Later members use the separate actual reset-plus-reload program instead.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.InitialSeed

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

include noQuantum in
private lemma input_systemCount : base.systemCount = 0 := by
  change base.quantumWires.length = 0
  rw [noQuantum]
  rfl

/-- The actual adjoined zero label is the physical zero of the newly owned bank. -/
lemma recyclingPrepare_bank_zero :
    preparedEmptyBasisEquiv base base.canonicalFreshKey (Arithmetic.layout width).toQuantum
        base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width)
        (input_systemCount base noQuantum)
        (BasisPreparation.zero (Arithmetic.layout width).toQuantum).value =
      (bankContext base noQuantum width).quantumLayout.zeroLabel := by
  funext wire
  obtain ⟨position, rfl⟩ := (PreparationBorrowed.fullPositionEquiv base base.canonicalFreshKey
    (Arithmetic.layout width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum width)).surjective wire
  cases position with
  | inl source =>
      apply Fin.ext
      exact preparedLocalBasisEquiv_new_value base base.canonicalFreshKey
        (Arithmetic.layout width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
        (allocationDisjoint base noQuantum width) (Arithmetic.layout width).toQuantum.zeroLabel
        (emptyContextBasis base (input_systemCount base noQuantum)) source
  | inr old => exact Fin.elim0 (Fin.cast (input_systemCount base noQuantum) old)

/-- Retaining the real result cells leaves every zero-valued bank coordinate unchanged. -/
lemma recyclingPrepare_cells_zero :
    MeasurementCells.basisEquiv (bankContext base noQuantum width) 2 (resultBits m ell)
        (bankContext base noQuantum width).quantumLayout.zeroLabel =
      (context base noQuantum m ell width).quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (MeasurementCells.wireEquiv (bankContext base noQuantum width)
    2 (resultBits m ell)).surjective target
  apply Fin.ext
  exact MeasurementCells.basisEquiv_value (bankContext base noQuantum width)
    2 (resultBits m ell) (bankContext base noQuantum width).quantumLayout.zeroLabel source

/-- Every complete actual store/reference block receives the seed after the first allocation. -/
lemma recyclingPrepare_seeded (N : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (Reload.seed base noQuantum m ell width N)
      ((prepare base noQuantum m ell width N).execute environment Reference state) := by
  let allocated : Circuit model base (bankContext base noQuantum width) :=
    .prepareZero base base.canonicalFreshKey (Arithmetic.layout width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (allocationDisjoint base noQuantum width)
  let retained := MeasurementCells.allocate (model := model)
    (bankContext base noQuantum width) 2 (resultBits m ell)
  have bankZero : BasisSeeded.Holds (bankContext base noQuantum width).quantumLayout.zeroLabel
      (allocated.execute environment Reference state) := by
    have actual := Circuit.prepareZero_empty_seeded (environment := environment)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (services := .empty) base.canonicalFreshKey
      (Arithmetic.layout width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
      (allocationDisjoint base noQuantum width) (input_systemCount base noQuantum) state
    rw [recyclingPrepare_bank_zero] at actual
    exact actual
  have cellsZero : BasisSeeded.Holds
      (context base noQuantum m ell width).quantumLayout.zeroLabel
      (retained.execute environment Reference (allocated.execute environment Reference state)) := by
    have actual := MeasurementCells.allocate_seeded (environment := environment) (model := model)
      (bankContext base noQuantum width) 2 (resultBits m ell)
      (bankContext base noQuantum width).quantumLayout.zeroLabel
      (allocated.execute environment Reference state) bankZero
    rw [recyclingPrepare_cells_zero] at actual
    exact actual
  exact BasisSeeded.seq (environment := environment) allocated (retained.seq (Reload.code base
    noQuantum m ell width N))
    (Reload.seed base noQuantum m ell width N) state
    (BasisSeeded.seq (environment := environment) retained (Reload.code base noQuantum m ell width
      N)
      (Reload.seed base noQuantum m ell width N) (allocated.execute environment Reference state)
      (Reload.recyclingReload_seeded base noQuantum m ell width N _ cellsZero))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.InitialSeed
