/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Probability
public import QuantumAlg.Core.Execution.Measurement.Cells.Laws
public import QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.State
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local

/-!
# Coherent-state law of the known-order sampler

The actual zero preparation, retained-cell allocation and native unitary
produce the pure state defined by the source circuit, on the same physical
wires and before the terminal Z measurements.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExecution

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma pre_systemCount : (pre : RuntimeCtx .quantum).systemCount = 0 := rfl

private lemma source_bank_wires (P : KnownOrderProblem G) :
    (OrderOracle.layout P).wires = (bankContext P).quantumLayout.wires :=
  ((RuntimeCtx.quantumLayout_wires (bankContext P)).trans (bankContext_wires P)).symm

private def bankBasisEquiv (P : KnownOrderProblem G) :
    (OrderOracle.layout P).Basis ≃ (bankContext P).register.Index :=
  preparedEmptyBasisEquiv pre pre.canonicalFreshKey (OrderOracle.layout P)
    bankFresh (bankDisjoint P) pre_systemCount

private def outputBasisEquiv (P : KnownOrderProblem G) :
    (OrderOracle.layout P).Basis ≃ (post P).register.Index :=
  (bankBasisEquiv P).trans
    (MeasurementCells.basisEquiv (bankContext P) 2 (sampleWidth P))

private lemma bankBasisEquiv_value (P : KnownOrderProblem G)
    (basis : (OrderOracle.layout P).Basis)
    (index : Fin (OrderPreparation.width P + OrderPreparation.width P + 1)) :
    (bankBasisEquiv P basis
      (Execution.positionsOfEqualWires (OrderOracle.layout P)
        (bankContext P).quantumLayout (source_bank_wires P) index)).val =
      (basis index).val := by
  let sameWires : (OrderOracle.layout P).wires =
      (pre.addOwnedLayout pre.canonicalFreshKey (OrderOracle.layout P)
        bankFresh (bankDisjoint P)).quantumLayout.wires := by
    simpa only [bankContext] using source_bank_wires P
  unfold bankBasisEquiv
  unfold bankContext
  change (preparedEmptyBasisEquiv pre pre.canonicalFreshKey
      (OrderOracle.layout P) bankFresh (bankDisjoint P) pre_systemCount basis
      (Execution.positionsOfEqualWires (OrderOracle.layout P)
        (pre.addOwnedLayout pre.canonicalFreshKey (OrderOracle.layout P)
          bankFresh (bankDisjoint P)).quantumLayout sameWires index)).val =
        (basis index).val
  rw [preparedEmptyBasisEquiv_eq_basisOfEqualWires pre pre.canonicalFreshKey
    (OrderOracle.layout P) bankFresh (bankDisjoint P) pre_systemCount
    sameWires]
  exact Execution.basisOfEqualWires_value (OrderOracle.layout P)
    (pre.addOwnedLayout pre.canonicalFreshKey (OrderOracle.layout P)
      bankFresh (bankDisjoint P)).quantumLayout sameWires basis index

private lemma outputBasisEquiv_eq (P : KnownOrderProblem G) :
    outputBasisEquiv P = (basisEquiv P).symm := by
  apply Equiv.ext
  intro basis
  funext target
  obtain ⟨index, rfl⟩ := (wireEquiv P).surjective target
  apply Fin.ext
  let bankIndex := Execution.positionsOfEqualWires (OrderOracle.layout P)
    (bankContext P).quantumLayout (source_bank_wires P) index
  have samePosition :
      MeasurementCells.wireEquiv (bankContext P) 2 (sampleWidth P) bankIndex =
        wireEquiv P index := by
    apply Fin.ext
    simp only [MeasurementCells.wireEquiv_val, bankIndex,
      Execution.positionsOfEqualWires, finCongr_apply_coe, wireEquiv]
  calc
    (outputBasisEquiv P basis (wireEquiv P index)).val =
        (bankBasisEquiv P basis bankIndex).val := by
      rw [← samePosition]
      exact MeasurementCells.basisEquiv_value (bankContext P) 2
        (sampleWidth P) (bankBasisEquiv P basis) bankIndex
    _ = (basis index).val := bankBasisEquiv_value P basis index
    _ = ((basisEquiv P).symm basis (wireEquiv P index)).val := by
      have corresponding := basisEquiv_wire_value P ((basisEquiv P).symm basis) index
      rw [Equiv.apply_symm_apply] at corresponding
      exact corresponding.symm

/-- Allocating the retained cells changes only the basis type of the local
quantum density operator. -/
public lemma allocationCode_localDensity (P : KnownOrderProblem G)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (bankContext P) Reference ((model P).HiddenState × H)) :
    ((allocationCode P).execute
      (sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex
        (S := (post P).register)
        (MeasurementCells.basisEquiv (bankContext P) 2 (sampleWidth P)) := by
  unfold allocationCode post
  rw [MeasurementCells.allocate_quantumMarginal]
  exact DensityOperator.reindex_prod_marginalLeft state.quantumMarginal
    (MeasurementCells.basisEquiv (bankContext P) 2 (sampleWidth P))

private lemma nativeProgram_input (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    DensityOperator.applyUnitary ((nativeProgram P expansion).matrix (OrderOracle.interpretation P))
      ((DensityOperator.ofPure
        (NormalizedVector.ket (R := (OrderOracle.layout P).register)
          (OrderOracle.layout P).zeroLabel)).reindex
          (S := (post P).register) (basisEquiv P).symm) =
      (DensityOperator.ofPure (OrderBornBridge.evolvedState P expansion)).reindex
          (S := (post P).register) (basisEquiv P).symm := by
  rw [basisEquiv_symm]
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix,
    ← DensityOperator.applyUnitary_reindex, ← DensityOperator.ofPure_apply]
  rfl

/-- The actual coherent prefix has exactly the source circuit's terminal pure
state, transported along the physical-wire correspondence. -/
public lemma beforeMeasurement_localDensity (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference ((model P).HiddenState × H))
    (normalized : state.IsNormalized) :
    ((beforeMeasurement P expansion).execute
      (sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (OrderBornBridge.evolvedState P expansion)).reindex
        (S := (post P).register) (basisEquiv P).symm := by
  have prepared := Circuit.prepareZero_empty_local_density
    (environment := sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := OrderOracle.model P)
    (operations := BitWord.model)
    (classicalOracles := ClassicalFiniteGroupOracle.model G)
    state pre.canonicalFreshKey (OrderOracle.layout P) bankFresh
    (bankDisjoint P) pre_systemCount normalized
  have preparedCode :
      ((preparationCode P).execute
      (sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure
          (BasisPreparation.zero (OrderOracle.layout P)).normalized).reindex
            (S := (bankContext P).register) (bankBasisEquiv P) := by
    unfold preparationCode bankBasisEquiv bankContext
    exact prepared
  have allocatedCode :
      ((allocationCode P).execute (sourceEnvironment P) Reference
          ((preparationCode P).execute
      (sourceEnvironment P) Reference state)).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure
          (BasisPreparation.zero (OrderOracle.layout P)).normalized).reindex
            (S := (post P).register) (outputBasisEquiv P) := by
    have allocated := allocationCode_localDensity P
      ((preparationCode P).execute (sourceEnvironment P) Reference state)
    rw [preparedCode] at allocated
    calc
      _ = ((DensityOperator.ofPure
            (BasisPreparation.zero (OrderOracle.layout P)).normalized).reindex
              (S := (bankContext P).register) (bankBasisEquiv P)).reindex
            (S := (post P).register)
            (MeasurementCells.basisEquiv (bankContext P) 2 (sampleWidth P)) := allocated
      _ = _ := by
        unfold outputBasisEquiv post
        exact DensityOperator.reindex_trans
          (DensityOperator.ofPure
            (BasisPreparation.zero (OrderOracle.layout P)).normalized)
          (bankBasisEquiv P)
          (MeasurementCells.basisEquiv (bankContext P) 2 (sampleWidth P))
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.unitary_localDensity, allocatedCode, outputBasisEquiv_eq]
  change DensityOperator.applyUnitary ((nativeProgram P expansion).matrix
      (OrderOracle.interpretation P))
      ((DensityOperator.ofPure
        (NormalizedVector.ket (R := (OrderOracle.layout P).register)
          (OrderOracle.layout P).zeroLabel)).reindex
          (S := (post P).register) (basisEquiv P).symm) = _
  exact nativeProgram_input P expansion

end

end QuantumAlg.FiniteCyclicDLP.OrderExecution
