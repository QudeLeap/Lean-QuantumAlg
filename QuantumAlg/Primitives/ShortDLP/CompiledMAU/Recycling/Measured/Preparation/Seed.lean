/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Preparation.Coordinates
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Actual complete-frame preparation supplies the measured member seed

The literal zero allocation, real retained output/vent cells and native X
loader establish the complete physical seed for arbitrary incoming Store,
hidden history and external-reference correlations [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev SeedCtx := context base noQuantum m ell width

/-- The actual complete physical identity seed in the original ordered wire placement. -/
def preparedSeed (N : Nat) : (SeedCtx base noQuantum m ell width).register.Index :=
  Placement.basis base noQuantum m ell width
    ((Physical.qubits width).basisEquiv.symm (seedLabel width N))

include noQuantum in
private lemma empty_systemCount : base.systemCount = 0 := by
  change base.quantumWires.length = 0
  rw [noQuantum]
  rfl

private lemma placed_zero :
    Placement.basis base noQuantum m ell width ((Physical.qubits width).basisEquiv.symm 0) =
      (SeedCtx base noQuantum m ell width).quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (positionsOfEqualWires (Physical.qubits width).toQuantum
    (SeedCtx base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width)).surjective target
  apply Fin.ext
  have same := basisOfEqualWires_value (Physical.qubits width).toQuantum
    (SeedCtx base noQuantum m ell width).quantumLayout (context_wires base noQuantum m ell width)
    ((Physical.qubits width).basisEquiv.symm 0) source
  refine same.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ (2 * width + 4))).val.testBit source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- Literal actual X loading takes the physical all-zero frame to the original seed. -/
lemma measuredLoad_apply_zero (environment : model.Environment) (N : Nat) :
    (load base noQuantum m ell width N).applyNormalized environment.quantum
        (NormalizedVector.ket (SeedCtx base noQuantum m ell width).quantumLayout.zeroLabel) =
      NormalizedVector.ket (preparedSeed base noQuantum m ell width N) := by
  have action :
      (load base noQuantum m ell width N).applyVec environment.quantum
          (HilbertVector.reindex (R := (Physical.qubits width).toQuantum.register)
            (S := (SeedCtx base noQuantum m ell width).register)
            (Placement.basis base noQuantum m ell width)
            (NormalizedVector.ket ((Physical.qubits width).basisEquiv.symm 0)).vec) =
        HilbertVector.reindex (R := (Physical.qubits width).toQuantum.register)
          (S := (SeedCtx base noQuantum m ell width).register)
          (Placement.basis base noQuantum m ell width)
          (NormalizedVector.ket
            ((Physical.qubits width).basisEquiv.symm (seedLabel width N))).vec := by
    change ((load base noQuantum m ell width N).matrix environment.quantum).applyVec _ = _
    rw [load, unitaryOfEqualWires_matrix]
    change (UnitaryOperator.reindex (Placement.basis base noQuantum m ell width)
      ((sourceLoad width N).matrix environment.quantum)).applyVec _ = _
    rw [UnitaryOperator.reindex_applyVec]
    exact congrArg (HilbertVector.reindex (R := (Physical.qubits width).toQuantum.register)
      (S := (SeedCtx base noQuantum m ell width).register)
      (Placement.basis base noQuantum m ell width))
      (congrArg (NormalizedVector.vec (R := (Physical.qubits width).toQuantum.register))
        (sourceLoad_zero (environment := environment.quantum) width N))
  rw [HilbertVector.reindex_ket, HilbertVector.reindex_ket, placed_zero] at action
  apply NormalizedVector.ext
  intro row
  exact congrArg (fun vector : HilbertVector (SeedCtx base noQuantum m ell width).register =>
    vector row) action

private lemma allocated_zero :
    preparedEmptyBasisEquiv base base.canonicalFreshKey (Physical.qubits width).toQuantum
        base.runtimeCtx_canonicalFreshKey_fresh (preparationDisjoint base noQuantum width)
        (empty_systemCount base noQuantum)
        (BasisPreparation.zero (Physical.qubits width).toQuantum).value =
      (bankContext base noQuantum width).quantumLayout.zeroLabel := by
  funext wire
  obtain ⟨position, rfl⟩ := (PreparationBorrowed.fullPositionEquiv base base.canonicalFreshKey
    (Physical.qubits width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
    (preparationDisjoint base noQuantum width)).surjective wire
  cases position with
  | inl source =>
      apply Fin.ext
      exact preparedLocalBasisEquiv_new_value base base.canonicalFreshKey
        (Physical.qubits width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
        (preparationDisjoint base noQuantum width) (Physical.qubits width).toQuantum.zeroLabel
        (emptyContextBasis base (empty_systemCount base noQuantum)) source
  | inr old => exact Fin.elim0 (Fin.cast (empty_systemCount base noQuantum) old)

private lemma retained_zero :
    MeasurementCells.basisEquiv (bankContext base noQuantum width) 2
        (resultBits m ell + (width - 2))
        (bankContext base noQuantum width).quantumLayout.zeroLabel =
      (SeedCtx base noQuantum m ell width).quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (MeasurementCells.wireEquiv (bankContext base noQuantum width)
    2 (resultBits m ell + (width - 2))).surjective target
  apply Fin.ext
  exact MeasurementCells.basisEquiv_value (bankContext base noQuantum width)
    2 (resultBits m ell + (width - 2))
    (bankContext base noQuantum width).quantumLayout.zeroLabel source

/-- The actual preparation establishes the complete seed internally for every original input. -/
lemma measuredPrepare_seeded (environment : model.Environment) (N : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (preparedSeed base noQuantum m ell width N)
      ((prepare base noQuantum m ell width N).execute environment Reference state) := by
  let allocated : Circuit model base (bankContext base noQuantum width) :=
    .prepareZero base base.canonicalFreshKey (Physical.qubits width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (preparationDisjoint base noQuantum width)
  let retained := MeasurementCells.allocate (model := model)
    (bankContext base noQuantum width) 2 (resultBits m ell + (width - 2))
  have bankZero : BasisSeeded.Holds (bankContext base noQuantum width).quantumLayout.zeroLabel
      (allocated.execute environment Reference state) := by
    have actual := Circuit.prepareZero_empty_seeded (environment := environment)
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (services := .empty) base.canonicalFreshKey
      (Physical.qubits width).toQuantum base.runtimeCtx_canonicalFreshKey_fresh
      (preparationDisjoint base noQuantum width) (empty_systemCount base noQuantum) state
    rw [allocated_zero] at actual
    exact actual
  have cellsZero : BasisSeeded.Holds
      (SeedCtx base noQuantum m ell width).quantumLayout.zeroLabel
      (retained.execute environment Reference (allocated.execute environment Reference state)) := by
    have actual := MeasurementCells.allocate_seeded (environment := environment) (model := model)
      (bankContext base noQuantum width) 2 (resultBits m ell + (width - 2))
      (bankContext base noQuantum width).quantumLayout.zeroLabel
      (allocated.execute environment Reference state) bankZero
    rw [retained_zero] at actual
    exact actual
  exact BasisSeeded.seq (environment := environment) allocated
    (retained.seq (.unitary (load base noQuantum m ell width N)))
    (preparedSeed base noQuantum m ell width N) state
    (BasisSeeded.seq (environment := environment) retained (.unitary (load base noQuantum m ell
      width N)) (preparedSeed base noQuantum m ell width N)
      (allocated.execute environment Reference state)
      (BasisSeeded.unitary (load base noQuantum m ell width N) environment _ _
        (measuredLoad_apply_zero base noQuantum m ell width environment N) _ cellsZero))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
