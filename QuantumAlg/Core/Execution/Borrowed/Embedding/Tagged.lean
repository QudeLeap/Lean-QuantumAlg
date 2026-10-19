/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.State
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Borrowed observations retaining a classical spectator tag

The spectator remains a classical label on the same complete borrowed quantum
and external-reference matrix. Decoding an orthogonal reference tag commutes
with this joint observation. No conditional state is normalized or required
to satisfy admission, and equality of separate marginals is never used
[dW19, qcnotes.tex:5381].
-/

namespace QuantumAlg.Execution

noncomputable section

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Keep a finite spectator label jointly with all actual borrowed systems and the reference. -/
def observeBorrowedTagged (read : H → Tag.Index) (state : State ctx Reference H) :
    ExecutionState (ctx.borrowedClassicalShape.Value × Tag.Index)
      (ctx.borrowedQuantumLayout.register.prod Reference) :=
  let classical := state.mapClassical fun record =>
    (record.1.readBorrowedClassical, read record.2)
  { block value := ctx.observeBorrowedWithReference Reference (classical.block value)
    total_le_one := by
      simp only [RuntimeCtx.observeBorrowedWithReference_mass]
      exact classical.total_le_one }

/-- The spectator observation preserves total mass, including subnormalized states. -/
lemma observeBorrowedTagged_mass (read : H → Tag.Index)
    (state : State ctx Reference H) : (observeBorrowedTagged read state).mass = state.mass := by
  unfold observeBorrowedTagged ExecutionState.mass
  simp only [RuntimeCtx.observeBorrowedWithReference_mass]
  exact state.mapClassical_mass _

/-- Each retained tag selects the original complete borrowed/reference matrix blocks. -/
lemma observeBorrowedTagged_entry (read : H → Tag.Index)
    (state : State ctx Reference H) (value : ctx.borrowedClassicalShape.Value) (tag : Tag.Index)
    (row column : ctx.borrowedQuantumLayout.Basis) (refRow refColumn : Reference.Index) :
    ((observeBorrowedTagged read state).block (value, tag)).matrix
      (row, refRow) (column, refColumn) =
      ∑ complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection,
        ∑ record : Store ctx × H,
          if (record.1.readBorrowedClassical, read record.2) = (value, tag) then
            (state.block record).matrix
              (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
                (ctx.borrowedBasisEquiv.symm row) complement, refRow)
              (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
                (ctx.borrowedBasisEquiv.symm column) complement, refColumn)
          else 0 := by
  change (ctx.observeBorrowedWithReference Reference
    ((state.mapClassical fun record =>
      (record.1.readBorrowedClassical, read record.2)).block (value, tag))).matrix
      (row, refRow) (column, refColumn) = _
  rw [RuntimeCtx.observeBorrowedWithReference_entry]
  simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply]

/-- History regrouping preserves the spectator selected from the same original record. -/
lemma observeBorrowedTagged_mapHistory (read : K → Tag.Index)
    (state : State ctx Reference H) (update : H → K) :
    observeBorrowedTagged read (state.mapHistory update) =
      observeBorrowedTagged (read ∘ update) state := by
  apply ExecutionState.ext
  intro label
  change ctx.observeBorrowedWithReference Reference
    (((state.mapHistory update).mapClassical fun record =>
      (record.1.readBorrowedClassical, read record.2)).block label) = _
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp]
  rfl

/-- Move only the mathematical tag coordinate before the complete borrowed/reference register. -/
def borrowedTagBasis :
    (ctx.borrowedQuantumLayout.register.prod (Tag.prod Reference)).Index ≃
      (Tag.prod (ctx.borrowedQuantumLayout.register.prod Reference)).Index where
  toFun value := (value.2.1, (value.1, value.2.2))
  invFun value := (value.2.1, (value.1, value.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Read the reference tag while retaining the full borrowed classical-quantum observation. -/
def decodeBorrowedTag
    (state : ExecutionState ctx.borrowedClassicalShape.Value
      (ctx.borrowedQuantumLayout.register.prod (Tag.prod Reference))) :
    ExecutionState (ctx.borrowedClassicalShape.Value × Tag.Index)
      (ctx.borrowedQuantumLayout.register.prod Reference) :=
  ExecutionState.decodeClassicalTag (state.reindex
    (borrowedTagBasis (ctx := ctx) (Reference := Reference) (Tag := Tag)))

/-- Tag decoding and joint borrowed observation retain exactly the same original CQ blocks. -/
lemma observeBorrowedTagged_decodeReferenceTag
    (state : State ctx (Tag.prod Reference) H) :
    observeBorrowedTagged Prod.snd (State.decodeReferenceTag state) =
      decodeBorrowedTag (observeBorrowed (Tag.prod Reference) state) := by
  apply ExecutionState.ext
  rintro ⟨value, tag⟩
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, refRow⟩
  rcases column with ⟨column, refColumn⟩
  rw [observeBorrowedTagged_entry, decodeBorrowedTag,
    ExecutionState.decodeClassicalTag_entry, ExecutionState.reindex_block_entry]
  change _ = ((observeBorrowed (Tag.prod Reference) state).block value).matrix
    (row, (tag, refRow)) (column, (tag, refColumn))
  rw [observeBorrowed_entry]
  apply Finset.sum_congr rfl
  intro complement _
  simp only [Fintype.sum_prod_type, Prod.mk.injEq, State.decodeReferenceTag_entry]
  apply Finset.sum_congr rfl
  intro store _
  apply Finset.sum_congr rfl
  intro history _
  by_cases same : store.readBorrowedClassical = value <;> simp [same]

end

end QuantumAlg.Execution
