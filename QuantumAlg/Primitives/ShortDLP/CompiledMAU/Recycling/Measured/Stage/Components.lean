/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Record
import all QuantumAlg.Core.Execution.Instrument.Execution

/-!
# Actual retained blocks of the measured stage's native components

These adapters preserve the full original Store, hidden state, chronological
path and external reference. They only restate already proved interpreter
equations in the retained-block composition form [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution EncodedBit.MeasuredUncompute
open MAU.Addition.Gidney.Measured.Instruction

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma deterministic_blocks {ctx : RuntimeCtx .quantum}
    (code : Circuit model ctx ctx false)
    (action : Store ctx → UnitaryOperator ctx.register) (path : Store ctx → code.Path)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (executed : code.execute environment Reference state =
      (state.applyUnitary fun entry =>
        UnitaryOperator.prodTensor (action entry.1) (1 : UnitaryOperator Reference)).mapClassical
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, path entry.1)))))
    (result : Store ctx × (model.HiddenState × (History × code.Path))) :
    ((code.execute environment Reference state).block result).matrix =
      ∑ original : Store ctx × (model.HiddenState × History), ∑ _outcome : Unit,
        if Execution.Instrument.retainedRecord (fun store (_ : Unit) => (store, path store))
          original () = result then
          (UnitaryOperator.prodTensor (action original.1) (1 : UnitaryOperator Reference) :
              HilbertOperator (ctx.register.prod Reference)) * (state.block original).matrix *
            (UnitaryOperator.prodTensor (action original.1) (1 : UnitaryOperator Reference) :
              HilbertOperator (ctx.register.prod Reference)).conjTranspose
        else 0 := by
  rw [executed, ExecutionState.mapClassical_block_matrix]
  simp only [Fintype.sum_unique, ExecutionState.applyUnitary_block,
    DensityOperator.applyUnitary_matrix]
  rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The literal native first H retains its original Store and Unit path. -/
lemma stageHadamard_block_matrix (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (result : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
          (allowAllocation := false) (single base noQuantum m ell width Gate.HOp)).Path))) :
    (((Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := false) (single base noQuantum m ell width Gate.HOp)).execute
        environment Reference state).block result).matrix =
      ∑ original : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ _outcome : Unit,
          if Execution.Instrument.retainedRecord (fun store (_ : Unit) => (store, ())) original ()
            = result then
            (UnitaryOperator.prodTensor
              ((single base noQuantum m ell width Gate.HOp).matrix environment.quantum)
              (1 : UnitaryOperator Reference) :
                HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)) *
              (state.block original).matrix *
              (UnitaryOperator.prodTensor
                ((single base noQuantum m ell width Gate.HOp).matrix environment.quantum)
                (1 : UnitaryOperator Reference) :
                  HilbertOperator ((Context base noQuantum m ell width).register.prod
                    Reference)).conjTranspose
          else 0 := by
  have actual := deterministic_blocks
    (Circuit.unitary (operations := BitWord.model) (classicalOracles := .empty)
      (allowAllocation := false) (single base noQuantum m ell width Gate.HOp))
    (fun _ => (single base noQuantum m ell width Gate.HOp).matrix environment.quantum)
    (fun _ => ()) environment Reference state
    ((Circuit.execute_unitary environment state
      (single base noQuantum m ell width Gate.HOp)).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)) result
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs <;> rfl

/-- Actual stored feedback contributes its selected native matrix and full chronological path. -/
lemma feedbackPrefix_block_matrix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (result : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History ×
        (feedbackPrefix base noQuantum m ell width inverse outputs position count bounded).Path))) :
    (((feedbackPrefix base noQuantum m ell width inverse outputs position count bounded).execute
      environment Reference state).block result).matrix =
      ∑ original : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ _outcome : Unit,
          if Execution.Instrument.retainedRecord (fun store (_ : Unit) => (store,
              feedbackPath base noQuantum m ell width inverse outputs position count bounded store))
              original () = result then
            (UnitaryOperator.prodTensor
              (feedbackAction base noQuantum m ell width environment.quantum inverse outputs
                position count bounded original.1) (1 : UnitaryOperator Reference) :
                  HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)) *
              (state.block original).matrix *
              (UnitaryOperator.prodTensor
                (feedbackAction base noQuantum m ell width environment.quantum inverse outputs
                  position count bounded original.1) (1 : UnitaryOperator Reference) :
                    HilbertOperator ((Context base noQuantum m ell width).register.prod
                      Reference)).conjTranspose
          else 0 := by
  exact deterministic_blocks
    (feedbackPrefix base noQuantum m ell width inverse outputs position count bounded)
    (feedbackAction base noQuantum m ell width environment.quantum inverse outputs position count
      bounded) (feedbackPath base noQuantum m ell width inverse outputs position count bounded)
    environment Reference state (feedbackPrefix_execute base noQuantum m ell width inverse outputs
      position count bounded environment Reference state) result

/-- The actual readout overwrites its real measured cell and retains the physical reset path. -/
def readoutRecord (resultCell : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (store : Store (Context base noQuantum m ell width))
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    Store (Context base noQuantum m ell width) ×
      (readout base noQuantum m ell width resultCell).Path :=
  (store.write (finiteOutput (control_qubit base noQuantum m ell width) resultCell)
      (.finite outcome),
    ((), (outcome, ⟨.finite outcome, ()⟩)))

/-- The actual H/MZ/reset adapter retains complete matrix-valued overwritten Store fibers. -/
lemma readout_retained_matrix
    (resultCell : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (result : Store (Context base noQuantum m ell width) ×
      (model.HiddenState × (History × (readout base noQuantum m ell width resultCell).Path))) :
    (((readout base noQuantum m ell width resultCell).execute environment Reference state).block
      result).matrix =
      ∑ original : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome,
          if Execution.Instrument.retainedRecord (readoutRecord base noQuantum m ell width
            resultCell) original
              outcome = result then
            krausOperator (oracles := .empty) (control base noQuantum m ell width)
                (control_qubit base noQuantum m ell width) environment.quantum outcome Reference *
              (state.block original).matrix *
                (krausOperator (oracles := .empty) (control base noQuantum m ell width)
                  (control_qubit base noQuantum m ell width) environment.quantum outcome
                  Reference).conjTranspose
          else 0 := by
  ext left right
  have actual := readout_block_matrix base noQuantum m ell width resultCell environment Reference
    state result left right
  refine actual.trans ?_
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  have sameRecord : Execution.Instrument.retainedRecord (readoutRecord base noQuantum m ell width
    resultCell)
      original outcome = record (oracles := .empty) (control base noQuantum m ell width)
        (control_qubit base noQuantum m ell width)
        (finiteOutput (control_qubit base noQuantum m ell width) resultCell) BitWord.model .empty
        original outcome := rfl
  by_cases selected : record (oracles := .empty) (control base noQuantum m ell width)
      (control_qubit base noQuantum m ell width)
      (finiteOutput (control_qubit base noQuantum m ell width) resultCell) BitWord.model .empty
      original outcome = result
  · simp only [if_pos selected, if_pos (sameRecord.trans selected)]
  · have notSelected : ¬ Execution.Instrument.retainedRecord (readoutRecord base noQuantum m ell
    width resultCell)
        original outcome = result := fun hit => selected (sameRecord.symm.trans hit)
    simp only [if_neg selected, if_neg notSelected, Matrix.zero_apply]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
