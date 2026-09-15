/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.State
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State

/-!
# One original finite-cyclic seed beneath all retained sample cells

Actual allocation of the bank and every sample cell establishes the original
zero exponents and encoded group identity in every complete store and reference block. The basis
  correspondence follows
the unchanged physical wires through finite-cell allocation. The original
literal circuit acts on exactly that column. Actual reset establishes the
same basis for every retained outcome and history, including zero-mass records.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical
namespace GateLevelAttempt.Native.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat) (ux : UxAccess P)

/-- Reindexing preserves each matrix entry of the original literal circuit. -/
theorem nativeFiniteCyclicBatch_member_matrix_entry
    (B : UniformSuperposition.BinaryExpansion P.order)
    (row column : (context base noQuantum P count).register.Index) :
    (member base noQuantum P count B ux).matrix row column =
      (GateLevelAttempt.quantumCircuit P B ux).matrix
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) row)
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) column) := rfl

/-- The actual seed column is precisely the original source circuit's normalized amplitude. -/
theorem nativeFiniteCyclicBatch_member_seed_amplitude
    (B : UniformSuperposition.BinaryExpansion P.order)
    (row : (context base noQuantum P count).register.Index) :
    (member base noQuantum P count B ux).matrix row (resetLabel base noQuantum P count ux) =
      ((GateLevelAttempt.quantumCircuit P B ux).applyNormalized
        (GateLevelAttempt.inputPreparation P B ux).normalized)
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) row) := by
  rw [nativeFiniteCyclicBatch_member_matrix_entry]
  simp only [resetLabel, Equiv.apply_symm_apply]
  exact (HilbertOperator.applyVec_ket
    ((GateLevelAttempt.quantumCircuit P B ux).matrix :
      HilbertOperator (Qubits (totalQubits P))) (tripleIndex 0 0 (ux.encode 1))
      (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) row)).symm

/-- Retaining the real finite outcome cells preserves the same original physical seed. -/
theorem nativeFiniteCyclicBatch_allocate_seeded
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (resetLabel base noQuantum P count ux)
      ((allocate base noQuantum P count ux).execute Reference state) := by
  have seeded := Native.nativeFiniteCyclic_prepare_seeded base noQuantum P ux state
  have measured := MeasurementCells.allocate_seeded (bankContext base noQuantum P) 2
    (count * sampleWidth P) _ ((Native.prepare base noQuantum P ux).execute Reference state) seeded
  rw [Native.cells_basis_agreement] at measured
  exact BasisSeeded.seq _ _ _ state measured

/-- Every incoming structural operand preserves its full reference weight during allocation. -/
theorem nativeFiniteCyclicBatch_allocate_reference {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate base noQuantum P count ux).execute Reference state)
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum P count input))) leftRef
        rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  let bankInput := input.underOwnedLayout base.canonicalFreshKey (bankLayout P)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum P)
  have sequence := Circuit.referenceFiberSum_execute_seq (Native.prepare base noQuantum P ux)
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (count * sampleWidth P)) state
    (fun store => weight (store.read (liftInput base noQuantum P count input))) leftRef rightRef
  have cells := MeasurementCells.allocate_referenceFiberSum_input bankInput 2 (count * sampleWidth
    P)
    ((Native.prepare base noQuantum P ux).execute Reference state) weight leftRef rightRef
  have prepared := Circuit.referenceFiberSum_execute_prepare_input input base.canonicalFreshKey
    (bankLayout P) base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum P)
    (preparation P ux) state weight leftRef rightRef
  exact sequence.trans (cells.trans prepared)

/-- Every actual reset record has the original seed and its complete conditional reference state. -/
theorem nativeFiniteCyclicBatch_reset_block_entry (slot : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum P count) Reference History)
    (record : Store (context base noQuantum P count) ×
      (History × (reset base noQuantum P count ux slot).Path))
    (left right : (context base noQuantum P count).register.Index) (leftRef rightRef :
      Reference.Index) :
    (((reset base noQuantum P count ux slot).execute Reference state).block record).matrix
        (left, leftRef) (right, rightRef) =
      if left = resetLabel base noQuantum P count ux ∧ right = resetLabel base noQuantum P count ux
        then
        (((reset base noQuantum P count ux slot).execute Reference state).block record).matrix
          (resetLabel base noQuantum P count ux, leftRef) (resetLabel base noQuantum P count ux,
            rightRef)
      else 0 :=
  QuditShift.resetToBasis_block_entry _ _ state record left right leftRef rightRef

end

end GateLevelAttempt.Native.Batch
end QuantumAlg.FiniteCyclicDLP.Canonical
