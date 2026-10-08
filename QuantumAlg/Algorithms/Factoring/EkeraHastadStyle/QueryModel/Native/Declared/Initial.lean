/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Born
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Actual zero seed of the declared EH sample

The real zero preparation and finite result-cell allocation establish the
member's physical zero in every complete store-reference block. No seed
assumption is placed on the incoming classical store or external reference.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

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
theorem prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History)) :
    BasisSeeded.Holds (Native.bankContext base noQuantum N).quantumLayout.zeroLabel
      ((prepare base noQuantum N input).execute Reference state) := by
  have empty : base.systemCount = 0 := by
    change base.quantumWires.length = 0
    rw [noQuantum]
    rfl
  have sameWires : (Native.layout N).wires =
      (Native.bankContext base noQuantum N).quantumLayout.wires :=
    ((Native.bankContext base noQuantum N).quantumLayout_wires.trans
      (Native.nativeOracle_bankContext_wires base noQuantum N)).symm
  have matched := preparedEmptyBasisEquiv_eq_basisOfEqualWires
    base base.canonicalFreshKey (Native.layout N)
    base.canonicalFreshKey_fresh (Native.allocationDisjoint base noQuantum N)
    empty sameWires (BasisPreparation.zero (Native.layout N)).value
  have sourceZero : (BasisPreparation.zero (Native.layout N)).value =
      (ShortDLP.layout (Native.parameters N)).binaryIndexEquiv.symm 0 := by
    funext index
    apply Fin.ext
    change 0 = (finTwoEquiv.symm
      ((0 : Fin (2 ^ ShortDLP.totalQubits (Native.parameters N))).val.testBit
        index.rev.val)).val
    simp only [Fin.val_zero, Nat.zero_testBit]
    rfl
  have mapped :
      (Execution.basisOfEqualWires (Native.layout N)
        (Native.bankContext base noQuantum N).quantumLayout sameWires)
          (BasisPreparation.zero (Native.layout N)).value =
        (Native.bankContext base noQuantum N).quantumLayout.zeroLabel := by
    rw [sourceZero]
    exact declared_basis_zero N
      (Native.nativeOracle_bankContext_wires base noQuantum N)
  have seed : preparedEmptyBasisEquiv base base.canonicalFreshKey (Native.layout N)
      base.canonicalFreshKey_fresh (Native.allocationDisjoint base noQuantum N)
      empty (BasisPreparation.zero (Native.layout N)).value =
        (Native.bankContext base noQuantum N).quantumLayout.zeroLabel :=
    matched.trans mapped
  have actual := Circuit.prepareZero_empty_seeded
    (gates := AlgorithmGate.model)
    (oracles := ShortDLP.declaredModel (Native.encoding input))
    (operations := BitWord.model)
    (services := ClassicalOracleModel.empty)
    base.canonicalFreshKey (Native.layout N)
    base.canonicalFreshKey_fresh (Native.allocationDisjoint base noQuantum N)
    empty state
  simpa +instances only [prepare, Native.bankContext, seed] using actual

/-- The actual result-cell and packed-output allocations keep the same zero
quantum support while preserving the original classical store. -/
theorem allocate_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (Native.bankContext base noQuantum N) Reference
      ((model input).HiddenState × History))
    (seeded : BasisSeeded.Holds
      (Native.bankContext base noQuantum N).quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (Native.context base noQuantum N).quantumLayout.zeroLabel
      ((allocate base noQuantum N input).execute Reference state) := by
  have measured := MeasurementCells.allocate_seeded (model := model input)
    (Native.bankContext base noQuantum N) 2 (measurementBits N)
    (Native.bankContext base noQuantum N).quantumLayout.zeroLabel state seeded
  rw [cells_basis_zero] at measured
  exact BasisSeeded.seq
    (MeasurementCells.allocate (model := model input)
      (Native.bankContext base noQuantum N) 2 (measurementBits N))
    (Circuit.retain (model := model input) (Native.cellsContext base noQuantum N)
      (Native.cellsContext base noQuantum N).canonicalFreshKey
      (.bits (measurementBits N))
      (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh)
    (Native.context base noQuantum N).quantumLayout.zeroLabel state
    (BasisSeeded.retain (model := model input)
      (ctx := Native.cellsContext base noQuantum N)
      (Native.cellsContext base noQuantum N).quantumLayout.zeroLabel
      ((MeasurementCells.allocate (model := model input)
        (Native.bankContext base noQuantum N) 2 (measurementBits N)).execute
          Reference state)
      measured (Native.cellsContext base noQuantum N).canonicalFreshKey
      (.bits (measurementBits N))
      (Native.cellsContext base noQuantum N).canonicalFreshKey_fresh)

/-- The actual prepared prefix establishes the selected member's seed from
every original input state. -/
theorem initial_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History)) :
    BasisSeeded.Holds (Native.context base noQuantum N).quantumLayout.zeroLabel
      ((allocate base noQuantum N input).execute Reference
        ((prepare base noQuantum N input).execute Reference state)) :=
  allocate_seeded base noQuantum N input _
    (prepare_seeded base noQuantum N input state)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
