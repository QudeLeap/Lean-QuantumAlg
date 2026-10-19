/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Program
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Context
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Local

/-!
# The one actual initial preparation establishes the sequential DLP seed

The quantum bank is prepared once from the empty executable input. Retaining
all result cells and the single shared reset scratch preserves each complete
store-reference zero block, with no initialization promise on the caller
[Sho95, source.tex:1713-1784].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G]

private lemma prepared_zero (P : KnownOrderProblem G) :
    preparedEmptyBasisEquiv pre pre.canonicalFreshKey (Binary.Oracle.layout P)
        bankFresh (bankDisjoint P) (by rfl) (Binary.Oracle.layout P).zeroLabel =
      (bankContext P).quantumLayout.zeroLabel := by
  have wires : (Binary.Oracle.layout P).wires = (bankContext P).quantumLayout.wires := by
    rw [RuntimeCtx.quantumLayout_wires]
    change _ = (Binary.Oracle.layout P).wires ++ []
    exact (List.append_nil _).symm
  rw [preparedEmptyBasisEquiv_eq_basisOfEqualWires pre pre.canonicalFreshKey
    (Binary.Oracle.layout P) bankFresh (bankDisjoint P) (by rfl) wires]
  funext target
  obtain ⟨index, rfl⟩ := (positionsOfEqualWires
    (Binary.Oracle.layout P) (bankContext P).quantumLayout wires).surjective target
  apply Fin.ext
  exact basisOfEqualWires_value (Binary.Oracle.layout P)
    (bankContext P).quantumLayout wires (Binary.Oracle.layout P).zeroLabel index

private lemma cells_zero (ctx : RuntimeCtx .quantum) (count : Nat) :
    MeasurementCells.basisEquiv ctx 2 count ctx.quantumLayout.zeroLabel =
      (MeasurementCells.context ctx 2 count).quantumLayout.zeroLabel := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

variable [Fintype G]

/-- The real prefix establishes zero in every complete stored block and reference extension. -/
private lemma initialCode_seeded (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference ((model P).HiddenState × History)) :
    BasisSeeded.Holds (context P count).quantumLayout.zeroLabel
      ((initialCode P count).execute (sourceEnvironment P) Reference state) := by
  have prepared := QuantumAlg.Circuit.prepareZero_empty_seeded
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := Binary.Oracle.model P)
    (operations := BitWord.model) (services := ClassicalFiniteGroupOracle.model G)
    pre.canonicalFreshKey (Binary.Oracle.layout P) bankFresh (bankDisjoint P) (by rfl) state
  change BasisSeeded.Holds
    (preparedEmptyBasisEquiv pre pre.canonicalFreshKey (Binary.Oracle.layout P)
      bankFresh (bankDisjoint P) (by rfl) (Binary.Oracle.layout P).zeroLabel)
    ((preparationCode P).execute (sourceEnvironment P) Reference state) at prepared
  rw [prepared_zero] at prepared
  let allocated := (MeasurementCells.allocate (model := model P) (bankContext P) 2
    (count * sampleWidth P)).execute
      (sourceEnvironment P) Reference ((preparationCode P).execute
        (sourceEnvironment P) Reference state)
  have samples := MeasurementCells.allocate_seeded
    (environment := sourceEnvironment P) (model := model P) (bankContext P)
    2 (count * sampleWidth P) (bankContext P).quantumLayout.zeroLabel
    ((preparationCode P).execute (sourceEnvironment P) Reference state) prepared
  rw [cells_zero] at samples
  have scratchReady := BasisSeeded.retain
    (environment := sourceEnvironment P) (model := model P)
    (sampleContext P count).quantumLayout.zeroLabel allocated samples
    (sampleContext P count).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count))
  have suffix := BasisSeeded.seq
    (environment := sourceEnvironment P)
    (MeasurementCells.allocate (model := model P) (bankContext P) 2 (count * sampleWidth P))
    (QuantumAlg.Circuit.retain (model := model P) (sampleContext P count)
      (sampleContext P count).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (sampleContext P count)))
    (context P count).quantumLayout.zeroLabel
    ((preparationCode P).execute (sourceEnvironment P) Reference state) scratchReady
  exact BasisSeeded.seq
    (environment := sourceEnvironment P) (preparationCode P) (allocationCode P count)
    (context P count).quantumLayout.zeroLabel state suffix

/-- Normalized input gives precisely the one actual initialized zero bank. -/
public lemma reusableDLP_initialCode_localDensity (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference ((model P).HiddenState × History))
    (normalized : state.IsNormalized) :
    ((initialCode P count).execute
      (sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
      DensityOperator.ofPure (NormalizedVector.ket (R := (context P count).register)
        (context P count).quantumLayout.zeroLabel) := by
  apply BasisSeeded.basisSeeded_localDensity
    ((initialCode P count).execute
      (sourceEnvironment P) Reference state) (context P count).quantumLayout.zeroLabel
    (initialCode_seeded P count state)
  exact (QuantumAlg.Circuit.execute_mass
    (environment := sourceEnvironment P) (initialCode P count) Reference state).trans normalized

end

end QuantumAlg.FiniteCyclicDLP.Reusable
