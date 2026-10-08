/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Born
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Sampling
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Seed
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Actual zero seed of the declared Shor sample

The real zero preparation and finite result-cell allocation establish the
member's physical zero in every complete store-reference block. No seed
assumption is placed on the incoming classical store or external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

private theorem cells_basis_zero (ctx : RuntimeCtx .quantum)
    (dimension : ℕ+) (count : Nat) :
    MeasurementCells.basisEquiv ctx dimension count ctx.quantumLayout.zeroLabel =
      (MeasurementCells.context ctx dimension count).quantumLayout.zeroLabel := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The actual initial allocation and zero preparation establish the declared
member's zero basis in every complete input-store and reference block. -/
theorem sampling_prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History)) :
    BasisSeeded.Holds (bankContext base noQuantum N).quantumLayout.zeroLabel
      ((Sampling.prepare base noQuantum N input).execute Reference state) := by
  have empty : base.systemCount = 0 := by
    change base.quantumWires.length = 0
    rw [noQuantum]
    rfl
  have sameWires : (layout N).wires =
      (bankContext base noQuantum N).quantumLayout.wires :=
    ((bankContext base noQuantum N).quantumLayout_wires.trans
      (bankContext_wires base noQuantum N)).symm
  have matched := preparedEmptyBasisEquiv_eq_basisOfEqualWires
    base base.canonicalFreshKey (layout N)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum N)
    empty sameWires (BasisPreparation.zero (layout N)).value
  have sourceZero : (BasisPreparation.zero (layout N)).value =
      (QuantumSignature.qubitsIndexEquiv (bankQubits N)).symm 0 := by
    funext index
    apply Fin.ext
    change 0 = (finTwoEquiv.symm
      ((0 : Fin (2 ^ bankQubits N)).val.testBit
        index.rev.val)).val
    simp only [Fin.val_zero, Nat.zero_testBit]
    rfl
  have mapped :
      (Execution.basisOfEqualWires (layout N)
        (bankContext base noQuantum N).quantumLayout sameWires)
          (BasisPreparation.zero (layout N)).value =
        (bankContext base noQuantum N).quantumLayout.zeroLabel := by
    rw [sourceZero]
    exact basis_zero N
      (bankContext_wires base noQuantum N)
  have seed : preparedEmptyBasisEquiv base base.canonicalFreshKey (layout N)
      base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum N)
      empty (BasisPreparation.zero (layout N)).value =
        (bankContext base noQuantum N).quantumLayout.zeroLabel :=
    matched.trans mapped
  have actual := Circuit.prepareZero_empty_seeded
    (gates := AlgorithmGate.model)
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model)
    (services := ClassicalOracleModel.empty)
    base.canonicalFreshKey (layout N)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum N)
    empty state
  simpa +instances only [Sampling.prepare, bankContext, seed] using actual

/-- Real result retention keeps the same zero bank in every complete reference block. -/
theorem allocate_seeded (ctx : RuntimeCtx .quantum) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (seeded : BasisSeeded.Holds ctx.quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (Storage.context ctx N).quantumLayout.zeroLabel
      ((allocate ctx N input).execute Reference state) := by
  let retention := Circuit.retain (model := executionModel input) ctx
    ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh
  have retained := BasisSeeded.retain (model := executionModel input)
    ctx.quantumLayout.zeroLabel state seeded ctx.canonicalFreshKey
    (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh
  have cells := MeasurementCells.allocate_seeded (model := executionModel input)
    (Storage.resultContext ctx N) 2 (phaseBits N)
    ctx.quantumLayout.zeroLabel (retention.execute Reference state) retained
  rw [show ctx.quantumLayout.zeroLabel =
    (Storage.resultContext ctx N).quantumLayout.zeroLabel from rfl, cells_basis_zero] at cells
  exact BasisSeeded.seq retention
    (MeasurementCells.allocate (model := executionModel input)
      (Storage.resultContext ctx N) 2 (phaseBits N))
    (Storage.context ctx N).quantumLayout.zeroLabel state cells

/-- The real prepare and sampler prefixes establish zero without a supplied state witness. -/
theorem prepared_sample_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History)) :
    BasisSeeded.Holds
      (Iteration.sampledContext (bankContext base noQuantum N) N).quantumLayout.zeroLabel
      ((Sampler.Retained.circuit (model := executionModel input)
        (bankContext base noQuantum N) N).execute Reference
          ((Sampling.prepare base noQuantum N input).execute Reference state)) :=
  Sampler.Retained.samplerRetained_seeded (model := executionModel input)
    (ctx := bankContext base noQuantum N) input
    (bankContext base noQuantum N).quantumLayout.zeroLabel _
    (sampling_prepare_seeded base noQuantum N input state)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
