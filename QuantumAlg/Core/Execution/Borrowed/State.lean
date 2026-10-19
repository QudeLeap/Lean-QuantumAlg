/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
public import QuantumAlg.Core.Execution.Store
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Joint observation of all borrowed classical and quantum systems

The actual borrowed classical values label their correlated borrowed quantum
and reference density operators. A single observation retains this entire CQ
object. Equality of its separate marginals is not substituted for equality of
the joint state [dW19, qcnotes.tex:5381].

The observations contain no additional runtime payload and emit no events.
The closed restoration predicate compares initial and final observations after
transport along the circuit's proved preservation of actual borrowed entries.
It carries no automatic proof of restoration and has no output-promise input.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {H : Type} [Fintype H]

/-- Observe borrowed classical values and their full joint quantum-reference blocks together. -/
def observeBorrowed (Reference : Register)
    (state : ExecutionState (Store ctx × H) (Register.prod ctx.register Reference)) :
    ExecutionState ctx.borrowedClassicalShape.Value
      (Register.prod ctx.borrowedQuantumLayout.register Reference) :=
  let classical := state.mapClassical fun label => label.1.readBorrowedClassical
  { block value := ctx.observeBorrowedWithReference Reference (classical.block value)
    total_le_one := by
      simp only [RuntimeCtx.observeBorrowedWithReference_mass]
      exact classical.total_le_one }

/-- Every borrowed classical label selects precisely the contributing actual store blocks. -/
lemma observeBorrowed_block (Reference : Register)
    (state : ExecutionState (Store ctx × H) (Register.prod ctx.register Reference))
    (value : ctx.borrowedClassicalShape.Value) :
    (observeBorrowed Reference state).block value =
      ctx.observeBorrowedWithReference Reference
        ((state.mapClassical fun label => label.1.readBorrowedClassical).block value) := rfl

/-- The joint CQ observation retains the complete execution probability mass. -/
lemma observeBorrowed_mass (Reference : Register)
    (state : ExecutionState (Store ctx × H) (Register.prod ctx.register Reference)) :
    (observeBorrowed Reference state).mass = state.mass := by
  calc
    (observeBorrowed Reference state).mass =
        (state.mapClassical fun label => label.1.readBorrowedClassical).mass := by
      unfold observeBorrowed ExecutionState.mass
      simp only [RuntimeCtx.observeBorrowedWithReference_mass]
    _ = state.mass := state.mapClassical_mass _

/-- One matrix entry sums only complement wires and source stores with the actual borrowed value. -/
lemma observeBorrowed_entry (Reference : Register)
    (state : ExecutionState (Store ctx × H) (Register.prod ctx.register Reference))
    (value : ctx.borrowedClassicalShape.Value)
    (row column : ctx.borrowedQuantumLayout.Basis) (refRow refColumn : Reference.Index) :
    ((observeBorrowed Reference state).block value).matrix (row, refRow) (column, refColumn) =
      ∑ complement : ctx.quantumLayout.ComplementBasis ctx.borrowedSelection,
        ∑ label : Store ctx × H,
          if label.1.readBorrowedClassical = value then
            (state.block label).matrix
              (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
                (ctx.borrowedBasisEquiv.symm row) complement, refRow)
              (ctx.quantumLayout.joinSelectedBasis ctx.borrowedSelection
                (ctx.borrowedBasisEquiv.symm column) complement, refColumn)
          else 0 := by
  rw [observeBorrowed_block, RuntimeCtx.observeBorrowedWithReference_entry]
  simp only [ExecutionState.mapClassical, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro complement _
  apply Finset.sum_congr rfl
  intro label _
  by_cases same : label.1.readBorrowedClassical = value
  · simp only [same, if_true]
  · simp only [same, if_false, Matrix.zero_apply]

/-- Transport a joint observation only along equality of its actual ordered interfaces. -/
def transportBorrowed {sourceShape targetShape : CShape}
    {sourceRegister targetRegister : Register} (Reference : Register)
    (sameShape : sourceShape = targetShape) (sameRegister : sourceRegister = targetRegister)
    (state : ExecutionState sourceShape.Value (Register.prod sourceRegister Reference)) :
    ExecutionState targetShape.Value (Register.prod targetRegister Reference) := by
  cases sameShape
  cases sameRegister
  exact state

/-- Equality transport retains every block and therefore its full probability mass. -/
lemma transportBorrowed_mass {sourceShape targetShape : CShape}
    {sourceRegister targetRegister : Register} (Reference : Register)
    (sameShape : sourceShape = targetShape) (sameRegister : sourceRegister = targetRegister)
    (state : ExecutionState sourceShape.Value (Register.prod sourceRegister Reference)) :
    (transportBorrowed Reference sameShape sameRegister state).mass = state.mass := by
  cases sameShape
  cases sameRegister
  rfl

/-- Equality transport is exactly the existing basis-and-classical relabeling. -/
lemma transportBorrowed_eq_reindex {sourceShape targetShape : CShape}
    {sourceRegister targetRegister : Register} (Reference : Register)
    (sameShape : sourceShape = targetShape) (sameRegister : sourceRegister = targetRegister)
    (state : ExecutionState sourceShape.Value (Register.prod sourceRegister Reference)) :
    transportBorrowed Reference sameShape sameRegister state =
      (state.reindex (S := Register.prod targetRegister Reference)
        ((Equiv.cast (congrArg Register.Index sameRegister)).prodCongr
          (Equiv.refl Reference.Index))).mapClassical
        (Equiv.cast (congrArg CShape.Value sameShape)) := by
  cases sameShape
  cases sameRegister
  change state = (state.reindex (Equiv.refl _)).mapClassical id
  rw [ExecutionState.reindex_refl, ExecutionState.mapClassical_id]

/-- Successive transports follow the equalities of the same ordered interfaces. -/
lemma transportBorrowed_trans {firstShape middleShape lastShape : CShape}
    {firstRegister middleRegister lastRegister : Register} (Reference : Register)
    (firstShapeEq : firstShape = middleShape) (secondShapeEq : middleShape = lastShape)
    (firstRegisterEq : firstRegister = middleRegister)
    (secondRegisterEq : middleRegister = lastRegister)
    (state : ExecutionState firstShape.Value (Register.prod firstRegister Reference)) :
    transportBorrowed Reference secondShapeEq secondRegisterEq
      (transportBorrowed Reference firstShapeEq firstRegisterEq state) =
        transportBorrowed Reference (firstShapeEq.trans secondShapeEq)
          (firstRegisterEq.trans secondRegisterEq) state := by
  cases firstShapeEq
  cases secondShapeEq
  cases firstRegisterEq
  cases secondRegisterEq
  rfl

/-- Put the final joint observation on exactly the input borrowed classical and quantum carriers. -/
def observeBorrowedAfter {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation)
    (Reference : Register)
    (state : ExecutionState (Store post × H) (Register.prod post.register Reference)) :
    ExecutionState pre.borrowedClassicalShape.Value
      (Register.prod pre.borrowedQuantumLayout.register Reference) :=
  transportBorrowed Reference code.borrowedClassicalShape_preserved
    code.borrowedRegister_preserved (observeBorrowed Reference state)

/-- Exact borrowed-coordinate transport preserves the full joint probability mass. -/
lemma observeBorrowedAfter_mass {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {allowAllocation : Bool}
    (code : Circuit model pre post allowAllocation)
    (Reference : Register)
    (state : ExecutionState (Store post × H) (Register.prod post.register Reference)) :
    (observeBorrowedAfter code Reference state).mass = state.mass := by
  rw [observeBorrowedAfter, transportBorrowed_mass, observeBorrowed_mass]

end Execution

namespace Circuit

/-- All borrowed classical-quantum-reference correlations are restored by the actual execution.
The final state is compared with the initial one as a single joint CQ object. -/
public def BorrowedRestored {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {allowAllocation : Bool} (code : Circuit model pre post allowAllocation) (Reference : Register)
    {H K : Type} [Fintype H] [Fintype K]
    (initial : ExecutionState (Execution.Store pre × H) (Register.prod pre.register Reference))
    (final : ExecutionState (Execution.Store post × K) (Register.prod post.register Reference)) :
    Prop :=
  Execution.observeBorrowedAfter code Reference final = Execution.observeBorrowed Reference initial

end Circuit

end

end QuantumAlg
