/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State

/-!
# Original finite-cyclic basis preparation and complete actual state

Actual allocation establishes the original zero exponents and encoded group identity
in every complete store and reference block. The basis correspondence follows
the unchanged physical wires through finite-cell allocation. The original
literal circuit acts on exactly that column. Actual reset establishes the
same basis for every retained outcome and history, including zero-mass records.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

private theorem cells_basis_agreement (P : KnownOrderProblem G) (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (bankLayout P).wires) (count : Nat)
    (original : (Qubits (totalQubits P)).Index) :
    MeasurementCells.basisEquiv ctx 2 count ((basisEquiv P sameWires).symm original) =
      (basisEquiv P (show (MeasurementCells.context ctx 2 count).quantumWires =
        (bankLayout P).wires from
          (MeasurementCells.context_quantumWires ctx 2 count).trans sameWires)).symm original := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (ux : UxAccess P)

/-- Reindexing preserves each matrix entry of the original literal circuit. -/
theorem nativeFiniteCyclic_member_matrix_entry
    (B : UniformSuperposition.BinaryExpansion P.order)
    (row column : (context base noQuantum P).register.Index) :
    (member base noQuantum P B ux).matrix row column =
      (GateLevelAttempt.quantumCircuit P B ux).matrix
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) row)
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) column) := rfl

/-- The actual seed column is precisely the original source circuit's normalized amplitude. -/
theorem nativeFiniteCyclic_member_seed_amplitude
    (B : UniformSuperposition.BinaryExpansion P.order)
    (row : (context base noQuantum P).register.Index) :
    (member base noQuantum P B ux).matrix row (resetLabel base noQuantum P ux) =
      ((GateLevelAttempt.quantumCircuit P B ux).applyNormalized
        (GateLevelAttempt.inputPreparation P B ux).normalized)
        (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) row) := by
  rw [nativeFiniteCyclic_member_matrix_entry]
  simp only [resetLabel, Equiv.apply_symm_apply]
  exact (HilbertOperator.applyVec_ket
    ((GateLevelAttempt.quantumCircuit P B ux).matrix :
      HilbertOperator (Qubits (totalQubits P))) (tripleIndex 0 0 (ux.encode 1))
      (basisEquiv P (nativeFiniteCyclic_context_wires base noQuantum P) row)).symm

/-- Actual quantum preparation establishes the original encoded-identity bank seed. -/
theorem nativeFiniteCyclic_prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds
      ((basisEquiv P (nativeFiniteCyclic_bankContext_wires base noQuantum P)).symm
        (tripleIndex 0 0 (ux.encode 1)))
      ((prepare base noQuantum P ux).execute Reference state) := by
  have empty : base.systemCount = 0 := by
    change base.quantumWires.length = 0
    rw [noQuantum]
    rfl
  have matched := preparedEmptyBasisEquiv_eq_basisOfEqualWires base base.canonicalFreshKey
    (bankLayout P) base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum P) empty
    (layoutWires P (nativeFiniteCyclic_bankContext_wires base noQuantum P)) (preparation P ux).value
  have actual := Circuit.prepare_empty_seeded base.canonicalFreshKey (bankLayout P)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum P)
    (preparation P ux) empty state
  rw [matched] at actual
  exact actual

/-- Retaining the real finite outcome cells preserves the same original physical seed. -/
theorem nativeFiniteCyclic_allocate_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (resetLabel base noQuantum P ux)
      ((allocate base noQuantum P ux).execute Reference state) := by
  have seeded := nativeFiniteCyclic_prepare_seeded base noQuantum P ux state
  have measured := MeasurementCells.allocate_seeded (bankContext base noQuantum P) 2
    (sampleWidth P) _ ((prepare base noQuantum P ux).execute Reference state) seeded
  rw [cells_basis_agreement] at measured
  exact BasisSeeded.seq _ _ _ state measured

/-- Every incoming structural operand preserves its full reference weight during allocation. -/
theorem nativeFiniteCyclic_allocate_reference {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate base noQuantum P ux).execute Reference state)
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum P input))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  let bankInput := input.underOwnedLayout base.canonicalFreshKey (bankLayout P)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum P)
  have sequence := Circuit.referenceFiberSum_execute_seq (prepare base noQuantum P ux)
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (sampleWidth P)) state
    (fun store => weight (store.read (liftInput base noQuantum P input))) leftRef rightRef
  have cells := MeasurementCells.allocate_referenceFiberSum_input bankInput 2 (sampleWidth P)
    ((prepare base noQuantum P ux).execute Reference state) weight leftRef rightRef
  have prepared := Circuit.referenceFiberSum_execute_prepare_input input base.canonicalFreshKey
    (bankLayout P) base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum P)
    (preparation P ux) state weight leftRef rightRef
  exact sequence.trans (cells.trans prepared)

/-- Every actual reset record has the original seed and its complete conditional reference state. -/
theorem nativeFiniteCyclic_reset_block_entry
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P) Reference History)
    (record : Store (context base noQuantum P) × (History × (reset base noQuantum P ux).Path))
    (left right : (context base noQuantum P).register.Index) (leftRef rightRef : Reference.Index) :
    (((reset base noQuantum P ux).execute Reference state).block record).matrix
        (left, leftRef) (right, rightRef) =
      if left = resetLabel base noQuantum P ux ∧ right = resetLabel base noQuantum P ux then
        (((reset base noQuantum P ux).execute Reference state).block record).matrix
          (resetLabel base noQuantum P ux, leftRef) (resetLabel base noQuantum P ux, rightRef)
      else 0 :=
  QuditShift.resetToBasis_block_entry _ _ state record left right leftRef rightRef

end

end GateLevelAttempt.Native
end QuantumAlg.FiniteCyclicDLP.Canonical
