/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics

/-!
# Complete allocation and reset states of the fixed Simon sampler

The actual retained slots, one quantum preparation and finite measurement
cells establish the original zero seed internally. Every earlier structural
input keeps its weighted complete reference operator. Later rounds use the
actual all-bank reset, which establishes that same seed for arbitrary old
classical values and arbitrary correlations with the reference. All execution
equations retain the original history and the actual paths.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original binary zero and the actual wirewise zero denote the same physical state. -/
theorem nativeSimon_basis_zero {ctx : RuntimeCtx .quantum} (n : Nat)
    (sameWires : ctx.quantumWires = (bankLayout n).wires) :
    (basisEquiv n sameWires).symm 0 = ctx.quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (wireEquiv n sameWires).surjective target
  apply Fin.ext
  have corresponding := Execution.basisOfEqualWires_value (bankLayout n)
    ctx.quantumLayout (layoutWires n sameWires)
    ((SimonsProblem.layout n).binaryIndexEquiv.symm 0) source
  refine corresponding.trans ?_
  change (finTwoEquiv.symm ((0 : Fin (2 ^ (2 * n))).val.testBit source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- Placement preserves every original circuit matrix entry, including its phase. -/
theorem nativeSimon_member_matrix_entry {ctx : RuntimeCtx .quantum} (n : Nat)
    (sameWires : ctx.quantumWires = (bankLayout n).wires) (sampling : SamplingCircuit n)
    (row column : ctx.register.Index) :
    (member n sameWires sampling).matrix row column =
      sampling.circuit.matrix (basisEquiv n sameWires row) (basisEquiv n sameWires column) := rfl

/-- The actual seed produces exactly the original normalized Born vector. -/
theorem nativeSimon_member_zero_amplitude {ctx : RuntimeCtx .quantum} (n : Nat)
    (sameWires : ctx.quantumWires = (bankLayout n).wires) (sampling : SamplingCircuit n)
    (row : ctx.register.Index) :
    (member n sameWires sampling).matrix row ctx.quantumLayout.zeroLabel =
      (sampling.circuit.applyNormalized (inputPreparation n).normalized)
        (basisEquiv n sameWires row) := by
  rw [← nativeSimon_basis_zero n sameWires, nativeSimon_member_matrix_entry,
    Equiv.apply_symm_apply]
  exact (HilbertOperator.applyVec_ket
    (sampling.circuit.matrix : HilbertOperator (Qubits (2 * n))) 0
      (basisEquiv n sameWires row)).symm

private theorem cells_basis_zero (ctx : RuntimeCtx .quantum) (dimension : ℕ+) (count : Nat) :
    MeasurementCells.basisEquiv ctx dimension count ctx.quantumLayout.zeroLabel =
      (MeasurementCells.context ctx dimension count).quantumLayout.zeroLabel := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

/-- Every original structural input keeps its reference weight through the actual slot retains. -/
theorem nativeSimon_allocateSlots_reference {base : RuntimeCtx .quantum} {shape : CShape}
    (n count : Nat) (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocateSlots base n count).execute Reference state)
      (fun entry _ => weight (entry.1.read (slotsInput n input count))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  induction count with
  | zero =>
      have executed := congrArg
        (fun output : State base Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ())))
        (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
  | succ count induction =>
      let middle := slots base n count
      let priorInput := slotsInput n input count
      let allocationPrefix := allocateSlots base n count
      let retention := Circuit.retain middle middle.canonicalFreshKey (.bits n)
        middle.canonicalFreshKey_fresh
      have sequence := Circuit.referenceFiberSum_execute_seq allocationPrefix retention state
        (fun store => weight (store.read (priorInput.underRetained middle.canonicalFreshKey
          (.bits n) middle.canonicalFreshKey_fresh))) leftRef rightRef
      have retained := Circuit.referenceFiberSum_execute_retain_input priorInput
        middle.canonicalFreshKey (.bits n) middle.canonicalFreshKey_fresh
        (allocationPrefix.execute Reference state) weight leftRef rightRef
      exact sequence.trans (retained.trans induction)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- The real preparation adjoins its original ket, pushes its owned entry and records its path. -/
theorem nativeSimon_prepare_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (slots base n count) Reference History) :
    (prepare base noQuantum n count).execute Reference state =
      (prepareContext state (slots base n count).canonicalFreshKey (bankLayout n)
        (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
        (preparation n).normalized).mapClassical
          (fun entry => (entry.1.pushOwnedLayout (slots base n count).canonicalFreshKey
            (bankLayout n) (slots base n count).canonicalFreshKey_fresh
            (allocationDisjoint base noQuantum n count), (entry.2, ()))) :=
  Circuit.execute_prepare state _ _ _ _ _

/-- All three real allocation stages retain their exact ordered paths and complete state. -/
theorem nativeSimon_allocate_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    (allocate base noQuantum n count).execute Reference state =
      ((MeasurementCells.allocate (bankContext base noQuantum n count) 2 n).execute Reference
        ((prepare base noQuantum n count).execute Reference
          ((allocateSlots base n count).execute Reference state))).mapHistory
            (fun history => (history.1.1.1, (history.1.1.2, (history.1.2, history.2)))) := by
  change ((Circuit.seq (allocateSlots base n count)
    ((prepare base noQuantum n count).seq
      (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n))).execute
        Reference state) = _
  rw [Circuit.execute_seq, Circuit.execute_seq, State.mapHistory_comp]
  rfl

/-- The actual preparation establishes zero in every complete store and reference block. -/
theorem nativeSimon_prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (slots base n count) Reference History) :
    BasisSeeded.Holds (bankContext base noQuantum n count).quantumLayout.zeroLabel
      ((prepare base noQuantum n count).execute Reference state) := by
  have empty : (slots base n count).systemCount = 0 := by
    change (slots base n count).quantumWires.length = 0
    rw [nativeSimon_slots_wires, noQuantum]
    rfl
  have sameWires := layoutWires n (nativeSimon_bankContext_wires base noQuantum n count)
  have matched := preparedEmptyBasisEquiv_eq_basisOfEqualWires (slots base n count)
    (slots base n count).canonicalFreshKey (bankLayout n)
    (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
    empty sameWires (preparation n).value
  have seed : preparedEmptyBasisEquiv (slots base n count)
      (slots base n count).canonicalFreshKey (bankLayout n)
      (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
      empty (preparation n).value = (bankContext base noQuantum n count).quantumLayout.zeroLabel :=
    matched.trans (nativeSimon_basis_zero n (nativeSimon_bankContext_wires base noQuantum n count))
  have actual := Circuit.prepare_empty_seeded (slots base n count).canonicalFreshKey (bankLayout n)
    (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
    (preparation n) empty state
  simpa +instances only [prepare, bankContext, seed] using actual

/-- The real allocator supplies the original seed without any incoming classical-value promise. -/
theorem nativeSimon_allocate_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (context base noQuantum n count).quantumLayout.zeroLabel
      ((allocate base noQuantum n count).execute Reference state) := by
  let retained := (allocateSlots base n count).execute Reference state
  have prepared := nativeSimon_prepare_seeded base noQuantum n count retained
  have measured := MeasurementCells.allocate_seeded (bankContext base noQuantum n count) 2 n
    (bankContext base noQuantum n count).quantumLayout.zeroLabel
    ((prepare base noQuantum n count).execute Reference retained) prepared
  rw [cells_basis_zero] at measured
  exact BasisSeeded.seq _ _ _ state (BasisSeeded.seq _ _ _ retained measured)

/-- The complete initial allocation preserves every earlier input's full reference weight. -/
theorem nativeSimon_allocate_reference {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate base noQuantum n count).execute Reference state)
      (fun entry _ => weight (entry.1.read (liftInput base noQuantum n count input)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  let oldInput := slotsInput n input count
  let bankInput := oldInput.underOwnedLayout (slots base n count).canonicalFreshKey
    (bankLayout n) (slots base n count).canonicalFreshKey_fresh
    (allocationDisjoint base noQuantum n count)
  let retained := (allocateSlots base n count).execute Reference state
  let prepared := (prepare base noQuantum n count).execute Reference retained
  have first := Circuit.referenceFiberSum_execute_seq (allocateSlots base n count)
    ((prepare base noQuantum n count).seq
      (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n)) state
    (fun store => weight (store.read (liftInput base noQuantum n count input))) leftRef rightRef
  have second := Circuit.referenceFiberSum_execute_seq (prepare base noQuantum n count)
    (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n) retained
    (fun store => weight (store.read (liftInput base noQuantum n count input))) leftRef rightRef
  have measured := MeasurementCells.allocate_referenceFiberSum_input bankInput 2 n
    prepared weight leftRef rightRef
  have preparation := Circuit.referenceFiberSum_execute_prepare_input oldInput
    (slots base n count).canonicalFreshKey (bankLayout n)
    (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
    (preparation n) retained weight leftRef rightRef
  exact first.trans (second.trans (measured.trans (preparation.trans
    (nativeSimon_allocateSlots_reference n count input state weight leftRef rightRef))))

/-- The actual scoped reset establishes zero support for every old complete store block. -/
theorem nativeSimon_reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference History) :
    BasisSeeded.Holds (context base noQuantum n count).quantumLayout.zeroLabel
      ((reset base noQuantum n count).execute Reference state) := by
  intro original left right leftRef rightRef
  have zeroEntry := ZReset.BankScope.zResetBankScope_complete_store_entry
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
    state original (context base noQuantum n count).quantumLayout.zeroLabel
    (context base noQuantum n count).quantumLayout.zeroLabel leftRef rightRef
  simp only [and_self] at zeroEntry
  exact (ZReset.BankScope.zResetBankScope_complete_store_entry
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
    state original left right leftRef rightRef).trans
      (congrArg (fun coefficient : ℂ =>
        if left = (context base noQuantum n count).quantumLayout.zeroLabel ∧
          right = (context base noQuantum n count).quantumLayout.zeroLabel then coefficient else 0)
        zeroEntry.symm)

/-- Reset preserves all old classical weights jointly with every reference matrix entry. -/
theorem nativeSimon_reset_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference History)
    (weight : Store (context base noQuantum n count) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((reset base noQuantum n count).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) leftRef rightRef := by
  refine (BasisSeeded.referenceFiberSum_seed _ _
    (nativeSimon_reset_seeded base noQuantum n count state) weight leftRef rightRef).trans ?_
  refine Eq.trans ?_ (BasisSeeded.fiber_store_blocks state
    (fun original _ => weight original) leftRef rightRef).symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  apply congrArg (fun coefficient : ℂ => weight original * coefficient)
  have actual := ZReset.BankScope.zResetBankScope_complete_store_entry
      (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
      state original (context base noQuantum n count).quantumLayout.zeroLabel
      (context base noQuantum n count).quantumLayout.zeroLabel leftRef rightRef
  simp only [and_self, if_true] at actual
  convert actual using 1
  congr 1

/-- Every later round retains the actual reset path before its real sampling path. -/
theorem nativeSimon_reusedSample_execute (sampling : SamplingCircuit n) (index : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference History) :
    (reusedSample base noQuantum n count sampling index).execute Reference state =
      ((sample base noQuantum n count sampling index).execute Reference
        ((reset base noQuantum n count).execute Reference state)).mapHistory
          (fun history => (history.1.1, (history.1.2, history.2))) :=
  Circuit.execute_seq _ _ state

end

end QuantumAlg.SimonsProblem.FixedSample.Native
