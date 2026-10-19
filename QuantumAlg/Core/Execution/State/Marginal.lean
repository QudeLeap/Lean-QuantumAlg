/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Base.State.Density

/-!
# Blockwise subsystem observations

Partial trace retains every actual classical label and its probability. It
commutes with deterministic classical observations and successive reference
projections, including off-diagonal entries on the retained quantum systems
[dW19, qcnotes.tex:5381,5394,6827]. These are mathematical observations of a
complete state, not instructions that discard or release caller storage.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

variable {C D : Type} [Fintype C] [Fintype D] {R S T : Register}

/-- Trace the right subsystem in each unchanged classical block. -/
@[expose] public def marginalLeft (state : ExecutionState C (R.prod S)) :
    ExecutionState C R where
  block value := (state.block value).marginalLeft
  total_le_one := by
    simpa only [DensityOperator.marginalLeft_mass] using state.total_le_one

/-- All retained coherences are the corresponding diagonal sum on the omitted subsystem. -/
public lemma executionState_marginalLeft_entry (state : ExecutionState C (R.prod S))
    (value : C) (row column : R.Index) :
    (state.marginalLeft.block value).matrix row column =
      ∑ basis : S.Index, (state.block value).matrix (row, basis) (column, basis) :=
  DensityOperator.marginalLeft_matrix (state.block value) row column

/-- Observing a subsystem preserves the mass of each original classical block. -/
public lemma executionState_marginalLeft_block_mass (state : ExecutionState C (R.prod S))
    (value : C) :
    (state.marginalLeft.block value).mass = (state.block value).mass :=
  DensityOperator.marginalLeft_mass (state.block value)

/-- The complete classical distribution remains normalized under subsystem observation. -/
public lemma executionState_marginalLeft_mass (state : ExecutionState C (R.prod S)) :
    state.marginalLeft.mass = state.mass := by
  simp only [mass, executionState_marginalLeft_block_mass]

/-- Classical observation and quantum partial trace sum the same complete state blocks. -/
public lemma executionState_marginalLeft_mapClassical [DecidableEq D]
    (state : ExecutionState C (R.prod S)) (read : C → D) :
    (state.mapClassical read).marginalLeft = state.marginalLeft.mapClassical read := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [executionState_marginalLeft_entry, mapClassical, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  by_cases same : read original = value
  · simp only [same, if_true]
  · simp only [same, if_false, Finset.sum_const_zero]

/-- Move only the reference coordinates so the first reference factor can be observed away. -/
@[expose] public def referenceFrameBasis :
    (R.prod (S.prod T)).Index ≃ ((R.prod T).prod S).Index where
  toFun value := ((value.1, value.2.2), value.2.1)
  invFun value := (value.1.1, (value.2, value.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Keep the original external reference while tracing a separate reference factor. -/
@[expose] public def forgetReferenceFrame (state : ExecutionState C (R.prod (S.prod T))) :
    ExecutionState C (R.prod T) :=
  (state.reindex (S := (R.prod T).prod S) referenceFrameBasis).marginalLeft

/-- The remaining reference coherences use the full diagonal sum on the frame. -/
public lemma executionState_forgetReferenceFrame_entry
    (state : ExecutionState C (R.prod (S.prod T))) (value : C)
    (row column : (R.prod T).Index) :
    ((state.forgetReferenceFrame).block value).matrix row column =
      ∑ frame : S.Index,
        (state.block value).matrix (row.1, (frame, row.2)) (column.1, (frame, column.2)) := by
  simp only [forgetReferenceFrame, executionState_marginalLeft_entry,
    reindex_block_entry, referenceFrameBasis, Equiv.coe_fn_symm_mk]

/-- Reference projection neither conditions nor renormalizes an input. -/
public lemma executionState_forgetReferenceFrame_mass
    (state : ExecutionState C (R.prod (S.prod T))) :
    state.forgetReferenceFrame.mass = state.mass :=
  (executionState_marginalLeft_mass _).trans (reindex_mass _ _)

/-- Both reference extensions have exactly the same local joint state. -/
public lemma executionState_forgetReferenceFrame_marginal
    (state : ExecutionState C (R.prod (S.prod T))) :
    state.forgetReferenceFrame.marginalLeft = state.marginalLeft := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  simp only [executionState_marginalLeft_entry, executionState_forgetReferenceFrame_entry]
  change (∑ reference : T.Index, ∑ frame : S.Index,
      (state.block value).matrix (row, (frame, reference)) (column, (frame, reference))) =
    ∑ pair : S.Index × T.Index,
      (state.block value).matrix (row, pair) (column, pair)
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

end

end QuantumAlg.ExecutionState
