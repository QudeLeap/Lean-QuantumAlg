/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Readout
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Execution.Measurement.Reference
import all QuantumAlg.Core.Execution.Random.Kernel.Discard
import all QuantumAlg.Core.Execution.Context.Embedding

/-!
# Complete external-reference observations under local operations

All local quantum and classical records are summed while arbitrary external
reference row and column coordinates are kept. These laws concern the complete
unconditioned state, including mixed inputs correlated with live storage
[dW19, qcnotes.tex:5381,5405,5409,6827].
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

namespace ExecutionState

variable {C : Type} [Fintype C] {R Reference : Register}

/-- The full reference observation traces only the original local register. -/
lemma referenceMarginal_entry (state : ExecutionState C (R.prod Reference))
    (row column : Reference.Index) :
    state.referenceMarginal.matrix row column =
      ∑ basis : R.Index, state.quantumMarginal.matrix (basis, row) (basis, column) := by
  rw [referenceMarginal, DensityOperator.marginalLeft_matrix]
  rfl

/-- Identical complete quantum marginals have identical complete reference observations. -/
lemma referenceMarginal_eq_of_quantumMarginal_eq {D : Type} [Fintype D]
    (first : ExecutionState C (R.prod Reference)) (second : ExecutionState D (R.prod Reference))
    (same : first.quantumMarginal = second.quantumMarginal) :
    first.referenceMarginal = second.referenceMarginal := by
  unfold referenceMarginal
  rw [same]

/-- Normalized stochastic transitions preserve the reference when all outcomes are retained. -/
lemma referenceMarginal_kernelChoice {Outcome : Type} [Fintype Outcome]
    (state : ExecutionState C (R.prod Reference)) (transition : C → PMF Outcome) :
    (Execution.kernelChoice state transition).referenceMarginal = state.referenceMarginal :=
  referenceMarginal_eq_of_quantumMarginal_eq _ _
    (Execution.kernelChoice_quantumMarginal state transition)

/-- Local unitaries preserve every external-reference coherence. -/
lemma referenceMarginal_applyLocalUnitary
    (state : ExecutionState C (R.prod Reference)) (program : C → UnitaryOperator R) :
    (state.applyUnitary (fun value =>
      UnitaryOperator.prodTensor (program value)
        (1 : UnitaryOperator Reference))).referenceMarginal = state.referenceMarginal := by
  apply DensityOperator.ext
  ext row column
  rw [referenceMarginal_entry, referenceMarginal_entry]
  exact applyLocalUnitary_reference_entry state program row column

/-- Summing all actual local measurement outcomes leaves the external reference unchanged. -/
lemma referenceMarginal_measureZ {count : Nat} (layout : QuantumLayout count)
    (wire : Fin count) (state : ExecutionState C (layout.register.prod Reference)) :
    (state.measureZ (fun basis => basis.1 wire)).referenceMarginal = state.referenceMarginal := by
  apply DensityOperator.ext
  ext row column
  rw [referenceMarginal_entry, referenceMarginal_entry]
  exact measureZ_reference_entry layout wire state row column

/-- A finite sum retains the sum of all complete reference matrices. -/
lemma referenceMarginal_finiteSum_entry {I : Type} [Fintype I]
    (states : I → ExecutionState C (R.prod Reference))
    (bounded : ∑ index, (states index).mass ≤ 1) (row column : Reference.Index) :
    (finiteSum states bounded).referenceMarginal.matrix row column =
      ∑ index, (states index).referenceMarginal.matrix row column := by
  simp only [referenceMarginal_entry, quantumMarginal, Matrix.sum_apply,
    finiteSum_block_matrix]
  calc
    _ = ∑ basis : R.Index, ∑ index : I, ∑ label : C,
        ((states index).block label).matrix (basis, row) (basis, column) := by
      apply Finset.sum_congr rfl
      intro basis _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Summing the actual classical dispatch fibers recovers the original complete reference. -/
lemma sum_referenceMarginal_selectClassical {D : Type} [Fintype D]
    (state : ExecutionState C (R.prod Reference)) (read : C → D)
    (row column : Reference.Index) :
    (∑ selected, (state.selectClassical read selected).referenceMarginal.matrix row column) =
      state.referenceMarginal.matrix row column := by
  have complete := congrArg
    (fun result : ExecutionState C (R.prod Reference) =>
      result.referenceMarginal.matrix row column) (finiteSum_selectClassical state read)
  rw [referenceMarginal_finiteSum_entry] at complete
  exact complete

end ExecutionState

namespace Execution.State

/-- Erasing or regrouping mathematical history preserves the entire reference observation. -/
lemma mapHistory_referenceMarginal {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference H) (update : H → K) :
    (state.mapHistory update).referenceMarginal = state.referenceMarginal :=
  ExecutionState.mapClassical_referenceMarginal state _

end Execution.State

namespace ContextEmbedding

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

private lemma referenceBasis_join (Reference : Register)
    (localValue : localCtx.register.Index) (frameValue : placement.frame.register.Index)
    (reference : Reference.Index) :
    placement.referenceBasis Reference
        (placement.basis.symm (localValue, frameValue), reference) =
      (localValue, (frameValue, reference)) := by
  change ((placement.basis (placement.basis.symm (localValue, frameValue))).1,
    ((placement.basis (placement.basis.symm (localValue, frameValue))).2, reference)) = _
  rw [Equiv.apply_symm_apply]

private lemma reindex_referenceMarginal_entry {C : Type} [Fintype C]
    {Reference : Register}
    (state : ExecutionState C (localCtx.register.prod (placement.frame.register.prod Reference)))
    (row column : Reference.Index) :
    (state.reindex (S := caller.register.prod Reference)
      (placement.referenceBasis Reference).symm).referenceMarginal.matrix row column =
      ∑ frame : placement.frame.register.Index,
        state.referenceMarginal.matrix (frame, row) (frame, column) := by
  simp only [ExecutionState.referenceMarginal_entry, ExecutionState.quantumMarginal,
    Matrix.sum_apply, ExecutionState.reindex_block_entry, Equiv.symm_symm]
  rw [← placement.basis.symm.sum_comp, Fintype.sum_prod_type]
  simp only [placement.referenceBasis_join]
  exact Finset.sum_comm

/-- Rejoining the context traces the complete frame when observing the old reference. -/
lemma contextEmbedding_join_referenceMarginal_entry {Reference : Register}
    {H : Type} [Fintype H]
    (state : State localCtx (placement.frame.register.prod Reference)
      (Store placement.frame × H)) (row column : Reference.Index) :
    (placement.join state).referenceMarginal.matrix row column =
      ∑ frame : placement.frame.register.Index,
        state.referenceMarginal.matrix (frame, row) (frame, column) := by
  rw [join, placement.reindex_referenceMarginal_entry,
    ExecutionState.mapClassical_referenceMarginal]

end ContextEmbedding

end

end QuantumAlg
