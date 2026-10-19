/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect.Embedding
import all QuantumAlg.Core.Execution.State.Effect
import all QuantumAlg.Core.Execution.Prepared.BasisSupport

/-!
# Observations pulled through actual basis preparation

The fresh basis value selects a subspace of the actual enlarged context. The
old register and arbitrary reference enter through the existing physical
allocation equivalence, and the Store update is the instruction's real update.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {Reference : Register} {count : Nat}

/-- Embed the old complete quantum/reference basis beside the actual prepared value. -/
def basisPreparationEmbedding (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    (Register.prod ctx.register Reference).Index →
      (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference).Index :=
  fun original => prepareContextBasisEquiv ctx Reference key layout fresh disjoint
    (preparation.value, original)

/-- The fresh value leaves every old quantum/reference coordinate distinguishable. -/
lemma basisPreparationEmbedding_injective (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    Function.Injective (basisPreparationEmbedding (Reference := Reference)
      key layout fresh disjoint preparation) := by
  intro left right equality
  exact congrArg Prod.snd
    ((prepareContextBasisEquiv ctx Reference key layout fresh disjoint).injective equality)

/-- Trace pairing with the actual prepared density is its compressed old-system effect. -/
lemma weight_preparedDensity (key : StorageKey) (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout)
    (state : DensityOperator (Register.prod ctx.register Reference))
    (effect : Effect
      (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference)) :
    effect.weight (preparedDensity key layout fresh disjoint preparation.normalized
      Reference state) =
      (Effect.compress (basisPreparationEmbedding key layout fresh disjoint preparation)
        (basisPreparationEmbedding_injective key layout fresh disjoint preparation) effect).weight
          state := by
  classical
  unfold Effect.weight
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Effect.compress_matrix,
    Matrix.submatrix_apply]
  let joined := prepareContextBasisEquiv ctx Reference key layout fresh disjoint
  have sumJoined (term :
      (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference).Index → ℂ) :
      (∑ basis, term basis) = ∑ newBasis, ∑ oldBasis, term (joined (newBasis, oldBasis)) :=
    (Equiv.sum_comp joined term).symm.trans (Fintype.sum_prod_type _)
  rw [sumJoined]
  simp_rw [sumJoined]
  simp only [joined, preparedDensity_joined_entry, BasisPreparation.normalized,
    NormalizedVector.ket_apply]
  simp [basisPreparationEmbedding, mul_ite, ite_mul]

namespace State

/-- The actual preparation pulls observations through its precise basis and Store embedding. -/
lemma effectWeight_prepare {H : Type} [Fintype H] (state : State ctx Reference H)
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout)
    (effects : Store (ctx.addOwnedLayout key layout fresh disjoint) × (H × Unit) →
      Effect (Register.prod (ctx.addOwnedLayout key layout fresh disjoint).register Reference)) :
    (state.prepare key layout fresh disjoint preparation).effectWeight effects =
      state.effectWeight (fun original =>
        Effect.compress (basisPreparationEmbedding key layout fresh disjoint preparation)
          (basisPreparationEmbedding_injective key layout fresh disjoint preparation)
          (effects (original.1.pushOwnedLayout key layout fresh disjoint, (original.2, ())))) := by
  unfold prepare
  rw [ExecutionState.effectWeight_mapClassical_decision]
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro original _
  exact weight_preparedDensity key layout fresh disjoint preparation (state.block original) _

end State

end

end QuantumAlg.Execution
