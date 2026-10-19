/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Program
public import QuantumAlg.Core.Execution.Reindex
public import QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.Preparation.Empty
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# Coherent-state law of the fresh-bank sampler

The actual zero preparation, cell allocation and parallel native family word
produce the independent pure product state before terminal measurements.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

open QuantumAlg.Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma pre_systemCount :
    (OrderExecution.pre : RuntimeCtx .quantum).systemCount = 0 := by
  change (RuntimeCtx.empty : RuntimeCtx .quantum).quantumWires.length = 0
  rw [RuntimeCtx.runtimeCtx_empty_quantumWires]
  rfl

private lemma source_bank_wires (P : KnownOrderProblem G) (count : Nat) :
    (layout P count).wires = (bankContext P count).quantumLayout.wires :=
  ((RuntimeCtx.quantumLayout_wires (bankContext P count)).trans
    (bankContext_wires P count)).symm

private def bankBasisEquiv (P : KnownOrderProblem G) (count : Nat) :
    (layout P count).register.Index ≃ (bankContext P count).register.Index :=
  preparedEmptyBasisEquiv OrderExecution.pre OrderExecution.pre.canonicalFreshKey
    (layout P count) OrderExecution.bankFresh (bankDisjoint P count) pre_systemCount

private def outputBasisEquiv (P : KnownOrderProblem G) (count : Nat) :
    (layout P count).register.Index ≃ (post P count).register.Index :=
  (bankBasisEquiv P count).trans
    (MeasurementCells.basisEquiv (bankContext P count) 2
      (count * OrderExecution.sampleWidth P))

private lemma bankBasisEquiv_value (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P count).register.Index) (index : Fin (count * bankSize P)) :
    (bankBasisEquiv P count basis
      (Execution.positionsOfEqualWires (layout P count)
        (bankContext P count).quantumLayout (source_bank_wires P count) index)).val =
      (basis index).val := by
  let sameWires : (layout P count).wires =
      (OrderExecution.pre.addOwnedLayout OrderExecution.pre.canonicalFreshKey
        (layout P count) OrderExecution.bankFresh (bankDisjoint P count)).quantumLayout.wires := by
    simpa only [bankContext] using source_bank_wires P count
  unfold bankBasisEquiv
  unfold bankContext
  change (preparedEmptyBasisEquiv OrderExecution.pre
      OrderExecution.pre.canonicalFreshKey (layout P count) OrderExecution.bankFresh
      (bankDisjoint P count) pre_systemCount basis
      (Execution.positionsOfEqualWires (layout P count)
        (OrderExecution.pre.addOwnedLayout OrderExecution.pre.canonicalFreshKey
          (layout P count) OrderExecution.bankFresh (bankDisjoint P count)).quantumLayout
        sameWires index)).val = (basis index).val
  rw [preparedEmptyBasisEquiv_eq_basisOfEqualWires OrderExecution.pre
    OrderExecution.pre.canonicalFreshKey (layout P count) OrderExecution.bankFresh
    (bankDisjoint P count) pre_systemCount sameWires]
  exact Execution.basisOfEqualWires_value (layout P count)
    (OrderExecution.pre.addOwnedLayout OrderExecution.pre.canonicalFreshKey
      (layout P count) OrderExecution.bankFresh (bankDisjoint P count)).quantumLayout
    sameWires basis index

private lemma outputBasisEquiv_eq (P : KnownOrderProblem G) (count : Nat) :
    outputBasisEquiv P count = (basisEquiv P count).symm := by
  apply Equiv.ext
  intro basis
  funext target
  let wireEquiv := Execution.positionsOfEqualWires (layout P count)
    (post P count).quantumLayout (sourceWires P count)
  obtain ⟨index, rfl⟩ := wireEquiv.surjective target
  apply Fin.ext
  let bankIndex := Execution.positionsOfEqualWires (layout P count)
    (bankContext P count).quantumLayout (source_bank_wires P count) index
  have samePosition :
      MeasurementCells.wireEquiv (bankContext P count) 2
          (count * OrderExecution.sampleWidth P) bankIndex =
        wireEquiv index := by
    apply Fin.ext
    simp only [MeasurementCells.wireEquiv_val, bankIndex,
      Execution.positionsOfEqualWires, finCongr_apply_coe, wireEquiv]
  calc
    (outputBasisEquiv P count basis (wireEquiv index)).val =
        (bankBasisEquiv P count basis bankIndex).val := by
      rw [← samePosition]
      exact MeasurementCells.basisEquiv_value (bankContext P count) 2
        (count * OrderExecution.sampleWidth P) (bankBasisEquiv P count basis) bankIndex
    _ = (basis index).val := bankBasisEquiv_value P count basis index
    _ = ((basisEquiv P count).symm basis (wireEquiv index)).val := by
      have corresponding := basisEquiv_wire_value P count
        ((basisEquiv P count).symm basis) index
      rw [Equiv.apply_symm_apply] at corresponding
      exact corresponding.symm

/-- Allocating all retained cells changes only the family basis type. -/
public lemma allocationCode_localDensity (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (bankContext P count) Reference
      ((OrderExecution.model P).HiddenState × H)) :
    ((allocationCode P count).execute
      (OrderExecution.sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
      state.quantumMarginal.marginalLeft.reindex
        (S := (post P count).register)
        (MeasurementCells.basisEquiv (bankContext P count) 2
          (count * OrderExecution.sampleWidth P)) := by
  unfold allocationCode post
  rw [MeasurementCells.allocate_quantumMarginal]
  exact DensityOperator.reindex_prod_marginalLeft state.quantumMarginal
    (MeasurementCells.basisEquiv (bankContext P count) 2
      (count * OrderExecution.sampleWidth P))

private lemma nativeFamilyProgram_input (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    DensityOperator.applyUnitary ((nativeFamilyProgram P count expansion).matrix
      (OrderOracle.interpretation P))
      ((DensityOperator.ofPure
        (NormalizedVector.ket (layout P count).zeroLabel)).reindex
          (S := (post P count).register) (basisEquiv P count).symm) =
      (DensityOperator.ofPure
        (physicalIndependentState P count expansion)).reindex
          (S := (post P count).register) (basisEquiv P count).symm := by
  rw [basisEquiv_symm]
  rw [nativeFamilyProgram, Execution.unitaryOfEqualWires_matrix,
    ← DensityOperator.applyUnitary_reindex, ← DensityOperator.ofPure_apply]
  let transport := Execution.basisOfEqualWires
    (layout P count) (post P count).quantumLayout (sourceWires P count)
  have evolved :
      DensityOperator.ofPure
          ((familyProgram P expansion count).applyNormalized (OrderOracle.interpretation P)
            (NormalizedVector.ket (layout P count).zeroLabel)) =
        DensityOperator.ofPure (physicalIndependentState P count expansion) :=
    congrArg DensityOperator.ofPure
      (familyProgram_applyNormalized_zero P count expansion)
  exact congrArg
    (fun density : DensityOperator (layout P count).register =>
      density.reindex (S := (post P count).register) transport) evolved

/-- The actual coherent batch prefix has exactly the independent product
state transported to the terminal runtime coordinates. -/
public lemma beforeMeasurement_localDensity (P : KnownOrderProblem G)
    (count : Nat) (expansion : OrderExpansion P.order)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State OrderExecution.pre Reference
      ((OrderExecution.model P).HiddenState × H))
    (normalized : state.IsNormalized) :
    ((beforeMeasurement P count expansion).execute
      (OrderExecution.sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure
        (physicalIndependentState P count expansion)).reindex
          (S := (post P count).register) (basisEquiv P count).symm := by
  have prepared := Circuit.prepareZero_empty_local_density
    (environment := OrderExecution.sourceEnvironment P)
    (gates := AlgorithmGate.model) (oracles := OrderOracle.model P)
    (operations := BitWord.model)
    (classicalOracles := ClassicalFiniteGroupOracle.model G)
    state OrderExecution.pre.canonicalFreshKey (layout P count)
    OrderExecution.bankFresh (bankDisjoint P count) pre_systemCount normalized
  have preparedCode :
      ((preparationCode P count).execute
        (OrderExecution.sourceEnvironment P) Reference state).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure (BasisPreparation.zero (layout P count)).normalized).reindex
          (S := (bankContext P count).register) (bankBasisEquiv P count) := by
    unfold preparationCode bankBasisEquiv bankContext
    exact prepared
  have allocatedCode :
      ((allocationCode P count).execute (OrderExecution.sourceEnvironment P) Reference
          ((preparationCode P count).execute
            (OrderExecution.sourceEnvironment P) Reference state)).quantumMarginal.marginalLeft =
        (DensityOperator.ofPure
          (BasisPreparation.zero (layout P count)).normalized).reindex
            (S := (post P count).register) (outputBasisEquiv P count) := by
    have allocated := allocationCode_localDensity P count
      ((preparationCode P count).execute (OrderExecution.sourceEnvironment P) Reference state)
    rw [preparedCode] at allocated
    calc
      _ = ((DensityOperator.ofPure
            (BasisPreparation.zero (layout P count)).normalized).reindex
              (S := (bankContext P count).register) (bankBasisEquiv P count)).reindex
            (S := (post P count).register)
            (MeasurementCells.basisEquiv (bankContext P count) 2
              (count * OrderExecution.sampleWidth P)) := allocated
      _ = _ := by
        unfold outputBasisEquiv post
        exact DensityOperator.reindex_trans
          (DensityOperator.ofPure
            (BasisPreparation.zero (layout P count)).normalized)
          (bankBasisEquiv P count)
          (MeasurementCells.basisEquiv (bankContext P count) 2
            (count * OrderExecution.sampleWidth P))
  rw [beforeMeasurement, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal,
    programs, Circuit.unitary_localDensity, allocatedCode,
    outputBasisEquiv_eq]
  change DensityOperator.applyUnitary ((nativeFamilyProgram P count expansion).matrix
    (OrderOracle.interpretation P))
      ((DensityOperator.ofPure
        (NormalizedVector.ket (layout P count).zeroLabel)).reindex
          (S := (post P count).register) (basisEquiv P count).symm) = _
  exact nativeFamilyProgram_input P count expansion

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch
