/- Exact Store coordinates and joins. -/

module

import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Composition.Coordinates

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

open QuantumAlg QuantumAlg.Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A quantum-only resident frame adds no unobserved classical Store fiber on rejoining. -/
lemma join_store_matrix_of_subsingleton_frame {kind : ProblemKind}
    {localCtx caller : RuntimeCtx kind} (placement : ContextEmbedding localCtx caller)
    [Subsingleton (Store placement.frame)] {Reference : Register}
    {History : Type} [Fintype History]
    (state : State localCtx (placement.frame.register.prod Reference)
      (Store placement.frame × History)) (stored : Store caller) :
    ((placement.join state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ((state.filterClassical
        (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix).submatrix
          (placement.referenceBasis Reference) (placement.referenceBasis Reference) := by
  have condition (original : Store localCtx × (Store placement.frame × History)) :
      ((placement.record History).symm original).1 = stored ↔
        original.1 = (placement.store stored).1 := by
    change placement.store.symm (original.1, original.2.1) = stored ↔ _
    constructor
    · intro same
      have mapped := congrArg (fun value : Store caller => (placement.store value).1) same
      exact (congrArg Prod.fst (placement.store.apply_symm_apply _)).symm.trans mapped
    · intro same
      apply placement.store.injective
      exact (placement.store.apply_symm_apply _).trans
        (Prod.ext same (Subsingleton.elim _ _))
  rw [← BasisSeeded.store_matrix]
  unfold ContextEmbedding.join
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  ext row column
  rw [ExecutionState.reindex_block_entry, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    Matrix.submatrix_apply, ExecutionState.filterClassical_matrix_weighted,
    ExecutionState.weightedMatrixEntry, Equiv.symm_symm, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro original _
  by_cases same : original.1 = (placement.store stored).1
  · rw [if_pos ((condition original).mpr same), if_pos same, one_mul]
  · rw [if_neg (fun actual => same ((condition original).mp actual)), if_neg same, zero_mul]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
