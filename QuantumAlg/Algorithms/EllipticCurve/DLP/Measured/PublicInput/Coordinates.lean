/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Store
import all QuantumAlg.Core.Execution.Context.Union.State.Laws

/-!
# Exact prescribed-input coordinates for the borrowed public frame

The public frame has two classical point inputs and no quantum systems.
Its unique quantum coordinate can therefore be reassociated with the same
external reference by an explicit equivalence. The prescribed input identity
retains every original classical block and every complex reference entry.
No public value enters at an intermediate execution stage.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem mapped_reindex {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {R S T : Register} (decisionB : DecidableEq B) (decisionC : DecidableEq C)
    (decisionD resultDecision : DecidableEq D) (state : ExecutionState A R)
    (first : A → B) (second : B → C) (third : C → D)
    (beforeBasis : R.Index ≃ S.Index) (afterBasis : S.Index ≃ T.Index) :
    (@ExecutionState.mapClassical C D _ _ S decisionD
      (@ExecutionState.mapClassical B C _ _ S decisionC
        ((@ExecutionState.mapClassical A B _ _ R decisionB state first).reindex beforeBasis)
          second) third).reindex afterBasis =
      (@ExecutionState.mapClassical A D _ _ R resultDecision state
        (third ∘ (second ∘ first))).reindex (beforeBasis.trans afterBasis) := by
  cases Subsingleton.elim decisionB (Classical.decEq B)
  cases Subsingleton.elim decisionC (Classical.decEq C)
  cases Subsingleton.elim decisionD (Classical.decEq D)
  cases Subsingleton.elim resultDecision (Classical.decEq D)
  rw [ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp, ExecutionState.reindex_trans]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem frameBasis_unique (value : (frame E exponentWidth).register.Index) :
    value = (frame E exponentWidth).quantumLayout.zeroLabel := by
  funext index
  have impossible := index.isLt
  have empty := frame_systemCount E exponentWidth
  omega

/-- The zero-system public frame retains precisely the original external reference coordinate. -/
def referenceEquiv (Reference : Register) : Reference.Index ≃
    (Register.prod (frame E exponentWidth).register Reference).Index where
  toFun label := ((frame E exponentWidth).quantumLayout.zeroLabel, label)
  invFun label := label.2
  left_inv _ := rfl
  right_inv label := by
    exact Prod.ext (frameBasis_unique E exponentWidth label.1).symm rfl

/-- Splitting the unchanged input wires retains their original complete basis label. -/
theorem beforeBasisEquiv_split
    (basis : (Allocation.before p.size (2 * exponentWidth)).register.Index) :
    unionBasisEquiv (Allocation.before p.size (2 * exponentWidth))
      (frame E exponentWidth) (before_disjoint E exponentWidth)
        (beforeBasisEquiv E exponentWidth basis) =
      (basis, (frame E exponentWidth).quantumLayout.zeroLabel) := by
  apply Prod.ext
  · funext index
    apply Fin.ext
    have splitValue := contextUnion_split_left_value
      (Allocation.before p.size (2 * exponentWidth)) (frame E exponentWidth)
      (before_disjoint E exponentWidth) (beforeBasisEquiv E exponentWidth basis) index
    have sameWires :
        (Allocation.before p.size (2 * exponentWidth)).quantumLayout.wires =
          (before E exponentWidth).quantumLayout.wires := by
      rw [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumLayout_wires, before_quantumWires]
    have samePosition :
        positionsOfEqualWires _ _ sameWires index =
          leftPosition (Allocation.before p.size (2 * exponentWidth))
            (frame E exponentWidth) (before_disjoint E exponentWidth) index := by
      apply Fin.ext
      rfl
    have originalValue := basisOfEqualWires_value _ _ sameWires basis index
    rw [samePosition] at originalValue
    exact splitValue.symm.trans originalValue
  · exact frameBasis_unique E exponentWidth _

/-- The original joint input basis splits only by adjoining the unique public quantum label. -/
theorem beforeJointBasisEquiv_split (Reference : Register)
    (basis : (Register.prod (Allocation.before p.size (2 * exponentWidth)).register
      Reference).Index) :
    referenceBasis (Allocation.before p.size (2 * exponentWidth))
      (frame E exponentWidth) (before_disjoint E exponentWidth) Reference
        (beforeJointBasisEquiv E exponentWidth Reference basis) =
      ((Equiv.refl (Allocation.before p.size (2 * exponentWidth)).register.Index).prodCongr
        (referenceEquiv E exponentWidth Reference)) basis := by
  change ((unionBasisEquiv _ _ _ (beforeBasisEquiv E exponentWidth basis.1)).1,
    ((unionBasisEquiv _ _ _ (beforeBasisEquiv E exponentWidth basis.1)).2, basis.2)) = _
  rw [beforeBasisEquiv_split]
  rfl

/-- The full initial state splits into the original state and its exact public history. -/
theorem initialState_split (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : ExecutionState (Store (Allocation.before p.size (2 * exponentWidth)))
      (Register.prod (Allocation.before p.size (2 * exponentWidth)).register Reference)) :
    splitState (Allocation.before p.size (2 * exponentWidth))
      (frame E exponentWidth) (before_disjoint E exponentWidth)
        ((initialState E exponentWidth problem original).mapClassical
          (fun value => (value, value))) =
      (original.mapClassical (fun value =>
        (value, (store E exponentWidth problem,
          initialStore E exponentWidth problem value)))).reindex
          (S := Register.prod (Allocation.before p.size (2 * exponentWidth)).register
            (Register.prod (frame E exponentWidth).register Reference))
          ((Equiv.refl (Allocation.before p.size (2 * exponentWidth)).register.Index).prodCongr
            (referenceEquiv E exponentWidth Reference)) := by
  have combined :
      splitState (Allocation.before p.size (2 * exponentWidth))
        (frame E exponentWidth) (before_disjoint E exponentWidth)
          ((initialState E exponentWidth problem original).mapClassical
            (fun value => (value, value))) =
      (original.mapClassical
        (recordEquiv (Allocation.before p.size (2 * exponentWidth))
          (frame E exponentWidth) (before_disjoint E exponentWidth)
          (Store (before E exponentWidth)) ∘
            ((fun value => (value, value)) ∘ initialStore E exponentWidth problem))).reindex
          (S := Register.prod (Allocation.before p.size (2 * exponentWidth)).register
            (Register.prod (frame E exponentWidth).register Reference))
          ((beforeJointBasisEquiv E exponentWidth Reference).trans
            (referenceBasis (Allocation.before p.size (2 * exponentWidth))
              (frame E exponentWidth) (before_disjoint E exponentWidth) Reference)) := by
    unfold splitState initialState
    exact mapped_reindex _ _ _ _ original _ _ _ _ _
  refine combined.trans ?_
  have labels :
      recordEquiv (Allocation.before p.size (2 * exponentWidth))
          (frame E exponentWidth) (before_disjoint E exponentWidth)
          (Store (before E exponentWidth)) ∘
        ((fun value => (value, value)) ∘ initialStore E exponentWidth problem) =
      (fun value =>
        (value, (store E exponentWidth problem, initialStore E exponentWidth problem value))) := by
    funext value
    change ((split (before_disjoint E exponentWidth)
      (join (before_disjoint E exponentWidth) value (store E exponentWidth problem))).1,
      ((split (before_disjoint E exponentWidth)
        (join (before_disjoint E exponentWidth) value (store E exponentWidth problem))).2,
          initialStore E exponentWidth problem value)) = _
    rw [split_join_store]
  rw [labels]
  congr 1
  ext basis
  exact beforeJointBasisEquiv_split E exponentWidth Reference basis

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
