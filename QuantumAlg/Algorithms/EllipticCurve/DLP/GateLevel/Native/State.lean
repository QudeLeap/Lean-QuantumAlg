/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State

/-!
# Original ECDLP basis preparation and complete actual state

Actual allocation establishes the original zero exponents and identity point
in every complete store and reference block. The basis correspondence follows
the unchanged physical wires through finite-cell allocation. The original
literal circuit acts on exactly that column. Actual reset establishes the
same basis for every retained outcome and history, including zero-mass records.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem cells_basis_agreement (I : ECDLPInstance E) (ctx : RuntimeCtx .quantum)
    (sameWires : ctx.quantumWires = (bankLayout I).wires) (count : Nat)
    (original : (Qubits (Layout.totalQubits I)).Index) :
    MeasurementCells.basisEquiv ctx 2 count ((basisEquiv I sameWires).symm original) =
      (basisEquiv I (show (MeasurementCells.context ctx 2 count).quantumWires =
        (bankLayout I).wires from
          (MeasurementCells.context_quantumWires ctx 2 count).trans sameWires)).symm original := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

/-- Reindexing preserves each matrix entry of the original literal circuit. -/
theorem nativeECDLP_member_matrix_entry (B : OrderExpansion (problem I).order) (A : Access I)
    (row column : (context base noQuantum I).register.Index) :
    (member base noQuantum I B A).matrix row column =
      (GateLevelAttempt.quantumCircuit I B A).matrix
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) row)
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) column) := rfl

/-- The actual seed column is precisely the original source circuit's normalized amplitude. -/
theorem nativeECDLP_member_seed_amplitude
    (B : OrderExpansion (problem I).order) (A : Access I)
    (row : (context base noQuantum I).register.Index) :
    (member base noQuantum I B A).matrix row (resetLabel base noQuantum I) =
      ((GateLevelAttempt.quantumCircuit I B A).applyNormalized (inputPreparation I).normalized)
        (basisEquiv I (nativeECDLP_context_wires base noQuantum I) row) := by
  rw [nativeECDLP_member_matrix_entry]
  simp only [resetLabel, Equiv.apply_symm_apply]
  exact (HilbertOperator.applyVec_ket
    ((GateLevelAttempt.quantumCircuit I B A).matrix :
      HilbertOperator (Qubits (Layout.totalQubits I))) (basisIndex I 0 0 1)
      (basisEquiv I (nativeECDLP_context_wires base noQuantum I) row)).symm

/-- Actual quantum preparation establishes the original identity-inclusive bank seed. -/
theorem nativeECDLP_prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds
      ((basisEquiv I (nativeECDLP_bankContext_wires base noQuantum I)).symm (basisIndex I 0 0 1))
      ((prepare base noQuantum I).execute Reference state) := by
  have empty : base.systemCount = 0 := by
    change base.quantumWires.length = 0
    rw [noQuantum]
    rfl
  have matched := preparedEmptyBasisEquiv_eq_basisOfEqualWires base base.canonicalFreshKey
    (bankLayout I) base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum I) empty
    (layoutWires I (nativeECDLP_bankContext_wires base noQuantum I)) (preparation I).value
  have actual := Circuit.prepare_empty_seeded base.canonicalFreshKey (bankLayout I)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum I) (preparation I) empty state
  rw [matched] at actual
  exact actual

/-- Retaining the real finite outcome cells preserves the same original physical seed. -/
theorem nativeECDLP_allocate_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (resetLabel base noQuantum I)
      ((allocate base noQuantum I).execute Reference state) := by
  have seeded := nativeECDLP_prepare_seeded base noQuantum I state
  have measured := MeasurementCells.allocate_seeded (bankContext base noQuantum I) 2
    (sampleWidth I) _ ((prepare base noQuantum I).execute Reference state) seeded
  rw [cells_basis_agreement] at measured
  exact BasisSeeded.seq _ _ _ state measured

/-- Every incoming structural operand preserves its full reference weight during allocation. -/
theorem nativeECDLP_allocate_reference {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate base noQuantum I).execute Reference state)
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  let bankInput := input.underOwnedLayout base.canonicalFreshKey (bankLayout I)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum I)
  have sequence := Circuit.referenceFiberSum_execute_seq (prepare base noQuantum I)
    (MeasurementCells.allocate (bankContext base noQuantum I) 2 (sampleWidth I)) state
    (fun store => weight (store.read (liftInput base noQuantum I input))) leftRef rightRef
  have cells := MeasurementCells.allocate_referenceFiberSum_input bankInput 2 (sampleWidth I)
    ((prepare base noQuantum I).execute Reference state) weight leftRef rightRef
  have prepared := Circuit.referenceFiberSum_execute_prepare_input input base.canonicalFreshKey
    (bankLayout I) base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum I)
    (preparation I) state weight leftRef rightRef
  exact sequence.trans (cells.trans prepared)

/-- Every actual reset record has the original seed and its complete conditional reference state. -/
theorem nativeECDLP_reset_block_entry {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History)
    (record : Store (context base noQuantum I) × (History × (reset base noQuantum I).Path))
    (left right : (context base noQuantum I).register.Index) (leftRef rightRef : Reference.Index) :
    (((reset base noQuantum I).execute Reference state).block record).matrix
        (left, leftRef) (right, rightRef) =
      if left = resetLabel base noQuantum I ∧ right = resetLabel base noQuantum I then
        (((reset base noQuantum I).execute Reference state).block record).matrix
          (resetLabel base noQuantum I, leftRef) (resetLabel base noQuantum I, rightRef)
      else 0 :=
  QuditShift.resetToBasis_block_entry _ _ state record left right leftRef rightRef

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
