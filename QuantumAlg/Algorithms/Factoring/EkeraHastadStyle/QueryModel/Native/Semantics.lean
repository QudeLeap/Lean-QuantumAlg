/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Program
import all QuantumAlg.Primitives.ShortDLP.BornProbability
import all QuantumAlg.Core.Execution.Preparation.Seed
import all QuantumAlg.Core.Execution.Prepared.LayoutAgreement
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Measurement.Matrix

/-!
# Complete state semantics of the original-width oracle sample

Actual preparation establishes the source zero state without restricting the
old classical store or reference. The selected operation keeps every original
store block and its complete reference operator. Actual measurement removes
precisely the coherences between unequal measured values; paid packing keeps
the real stored outcomes and the complete original history.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The source binary zero is exactly the actual wirewise zero state. -/
theorem nativeOracle_basis_zero {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) :
    (basisEquiv N sameWires).symm 0 = ctx.quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (wireEquiv N sameWires).surjective target
  apply Fin.ext
  have corresponding := Execution.basisOfEqualWires_value (layout N)
    ctx.quantumLayout (layoutWires N sameWires)
    ((ShortDLP.layout (parameters N)).binaryIndexEquiv.symm 0) source
  refine corresponding.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ ShortDLP.totalQubits (parameters N))).val.testBit source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- Every placed source matrix entry retains its exact complex amplitude. -/
theorem nativeOracle_member_matrix_entry {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) (input : Input N)
    (parameter : (ParameterShape N).Value) (row column : ctx.register.Index) :
    (member N sameWires input parameter).matrix row column =
      (ShortDLP.circuit (encoding input)
        (parameterUnit parameter) (parameterTarget parameter)).matrix
        (basisEquiv N sameWires row) (basisEquiv N sameWires column) := rfl

/-- The actual zero input produces the original Born vector, including every phase. -/
theorem nativeOracle_member_zero_amplitude {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) (input : Input N)
    (parameter : (ParameterShape N).Value) (row : ctx.register.Index) :
    (member N sameWires input parameter).matrix row ctx.quantumLayout.zeroLabel =
      (ShortDLP.BornProbability.evolvedState (encoding input)
        (parameterUnit parameter) (parameterTarget parameter)).normalized
          (basisEquiv N sameWires row) := by
  rw [← nativeOracle_basis_zero N sameWires, nativeOracle_member_matrix_entry,
    Equiv.apply_symm_apply]
  exact (HilbertOperator.applyVec_ket
    ((ShortDLP.circuit (encoding input) (parameterUnit parameter)
      (parameterTarget parameter)).matrix : HilbertOperator
        (Qubits (ShortDLP.totalQubits (parameters N)))) 0 (basisEquiv N sameWires row)).symm

private theorem cells_basis_zero (ctx : RuntimeCtx .quantum) (dimension : ℕ+) (count : Nat) :
    MeasurementCells.basisEquiv ctx dimension count ctx.quantumLayout.zeroLabel =
      (MeasurementCells.context ctx dimension count).quantumLayout.zeroLabel := by
  induction count with
  | zero => rfl
  | succ count induction => exact induction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Actual preparation establishes zero in every complete store-reference block. -/
theorem nativeOracle_prepare_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (bankContext base noQuantum N).quantumLayout.zeroLabel
      ((prepare base noQuantum N).execute Reference state) := by
  have empty : base.systemCount = 0 := by
    change base.quantumWires.length = 0
    rw [noQuantum]
    rfl
  have sameWires := layoutWires N (nativeOracle_bankContext_wires base noQuantum N)
  have matched := preparedEmptyBasisEquiv_eq_basisOfEqualWires base base.canonicalFreshKey
    (layout N) base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum N) empty
    sameWires (preparation N).value
  have seed : preparedEmptyBasisEquiv base base.canonicalFreshKey (layout N)
      base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum N) empty
        (preparation N).value = (bankContext base noQuantum N).quantumLayout.zeroLabel :=
    matched.trans (nativeOracle_basis_zero N (nativeOracle_bankContext_wires base noQuantum N))
  have actual := Circuit.prepare_empty_seeded base.canonicalFreshKey (layout N)
    base.canonicalFreshKey_fresh (allocationDisjoint base noQuantum N) (preparation N) empty state
  simpa +instances only [prepare, bankContext, seed] using actual

/-- Every actual result allocation preserves that same complete zero support. -/
theorem nativeOracle_allocate_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (bankContext base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (bankContext base noQuantum N).quantumLayout.zeroLabel state) :
    BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel
      ((allocate base noQuantum N).execute Reference state) := by
  have measured := MeasurementCells.allocate_seeded (bankContext base noQuantum N) 2
    (measurementBits N) (bankContext base noQuantum N).quantumLayout.zeroLabel state seeded
  rw [cells_basis_zero] at measured
  exact BasisSeeded.seq _ _ (context base noQuantum N).quantumLayout.zeroLabel state
    (BasisSeeded.retain (cellsContext base noQuantum N).quantumLayout.zeroLabel
      ((MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)).execute
        Reference state) measured (cellsContext base noQuantum N).canonicalFreshKey
          (.bits (measurementBits N)) (cellsContext base noQuantum N).canonicalFreshKey_fresh)

/-- The actual initial prefix establishes the member seed internally for every original state. -/
theorem nativeOracle_initial_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) :
    BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel
      ((allocate base noQuantum N).execute Reference
        ((prepare base noQuantum N).execute Reference state)) :=
  nativeOracle_allocate_seeded base noQuantum N _
    (nativeOracle_prepare_seeded base noQuantum N state)

/-- The stored parameter selects the same unitary and is retained in the actual branch path. -/
theorem nativeOracle_selected_execute (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (selected base noQuantum N input parameter).execute Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (member N (nativeOracle_context_wires base noQuantum N) input
          (entry.1.read (liftInput base noQuantum N parameter))).matrix
        (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1,
            (entry.2, ⟨entry.1.read (liftInput base noQuantum N parameter), ()⟩))) :=
  Circuit.selectedUnitary_execute _ _ _ state

/-- Each complete store has the original source outer product and its entire reference entry. -/
theorem nativeOracle_selected_seed_entry (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (seeded : BasisSeeded.Holds (context base noQuantum N).quantumLayout.zeroLabel state)
    (original : Store (context base noQuantum N))
    (left right : (context base noQuantum N).register.Index) (leftRef rightRef : Reference.Index) :
    (((selected base noQuantum N input parameter).execute Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      (ShortDLP.BornProbability.evolvedState (encoding input)
        (parameterUnit (original.read (liftInput base noQuantum N parameter)))
        (parameterTarget (original.read (liftInput base noQuantum N parameter)))).normalized
          (basisEquiv N (nativeOracle_context_wires base noQuantum N) left) *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((context base noQuantum N).quantumLayout.zeroLabel, leftRef)
          ((context base noQuantum N).quantumLayout.zeroLabel, rightRef) *
        star ((ShortDLP.BornProbability.evolvedState (encoding input)
          (parameterUnit (original.read (liftInput base noQuantum N parameter)))
          (parameterTarget (original.read (liftInput base noQuantum N parameter)))).normalized
            (basisEquiv N (nativeOracle_context_wires base noQuantum N) right)) := by
  dsimp +instances only [selected]
  rw [Circuit.selectedUnitary_store_matrix]
  rw [BasisSeeded.unitary_entry _ state seeded]
  rw [nativeOracle_member_zero_amplitude, nativeOracle_member_zero_amplitude]

private theorem measured_packed_entry {ctx : RuntimeCtx .quantum}
    (readouts : List (ZReadout ctx)) {input output : CShape}
    (pack : ClassicalOp input output ctx ctx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (weight : Store ctx × (History × ((Circuit.measurementSequence readouts).Path × Unit)) → ℂ)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      (((Circuit.measurementSequence readouts).seq (.classical pack)).execute Reference state)
      weight (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree readouts left right then
        ExecutionState.weightedMatrixEntry state (fun entry => weight
          ((Circuit.writeMeasurementPath readouts entry.1
            (Circuit.measurementBasisPath readouts left)).applyOp pack,
            (entry.2, (Circuit.measurementBasisPath readouts left, ()))))
              (left, leftRef) (right, rightRef)
      else 0 := by
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical,
    Circuit.execute_classical_mapClassical]
  exact Circuit.measurementSequence_weightedMatrixEntry readouts state _ left right leftRef rightRef

/-- Actual measured and packed entries preserve every unmeasured coherence and complete history. -/
theorem nativeOracle_body_weighted_entry (input : Input N)
    (parameter : CInputRef base (ParameterShape N))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : Store (context base noQuantum N) ×
      (History × (body base noQuantum N input parameter).Path) → ℂ)
    (left right : (context base noQuantum N).register.Index) (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((body base noQuantum N input parameter).execute Reference state)
      weight (left, leftRef) (right, rightRef) =
      if Circuit.measurementLabelsAgree (readouts base noQuantum N) left right then
        ExecutionState.weightedMatrixEntry
          ((selected base noQuantum N input parameter).execute Reference state) (fun entry => weight
            ((Circuit.writeMeasurementPath (readouts base noQuantum N) entry.1
              (Circuit.measurementBasisPath (readouts base noQuantum N) left)).applyOp
                (packing base noQuantum N),
              (entry.2.1, (entry.2.2,
                (Circuit.measurementBasisPath (readouts base noQuantum N) left, ())))))
                  (left, leftRef) (right, rightRef)
      else 0 := by
  dsimp +instances only [body] at weight ⊢
  rw [Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.weightedMatrixEntry_mapClassical]
  exact measured_packed_entry (readouts base noQuantum N) (packing base noQuantum N)
    ((selected base noQuantum N input parameter).execute Reference state)
    _ left right leftRef rightRef

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native
