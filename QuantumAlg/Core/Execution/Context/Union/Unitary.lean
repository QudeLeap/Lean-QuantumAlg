/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Context.Union.Basis
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Execution.Context.Union.Basis
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Actual unitary instructions in a disjoint runtime frame

Tensor syntax places the original program beside identity on every actual
right-context wire. The exact union coordinates then identify that tensor
with the complete runtime register [dW19, qcnotes.tex:389]. No physical wire
is allocated, removed or relabelled. The event trace and its resource pool
are unchanged; the symbolic depth retains the tensor identity node.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} (left right : RuntimeCtx .quantum)
  (disjoint : RuntimeCtx.StorageDisjoint left right)
  (program : UnitaryCircuit gates oracles left.quantumLayout)
  (environment : oracles.Interpretation)

private def leftPlacement : QuantumLayout.Embedding left.quantumLayout
    (left.disjointUnion right disjoint).quantumLayout where
  position :=
    { toFun := leftPosition left right disjoint
      inj' := fun _ _ same =>
        Sum.inl.inj ((unionPositionEquiv left right disjoint).injective same) }
  wire_eq := contextUnion_left_wire left right disjoint

private def rightPlacement : QuantumLayout.Embedding right.quantumLayout
    (left.disjointUnion right disjoint).quantumLayout where
  position :=
    { toFun := rightPosition left right disjoint
      inj' := fun _ _ same =>
        Sum.inr.inj ((unionPositionEquiv left right disjoint).injective same) }
  wire_eq := contextUnion_right_wire left right disjoint

private lemma placements_disjoint :
    Disjoint (leftPlacement left right disjoint).selection
      (rightPlacement left right disjoint).selection := by
  apply Finset.disjoint_left.mpr
  intro wire inLeft inRight
  obtain ⟨first, _, first_eq⟩ := Finset.mem_map.mp inLeft
  obtain ⟨second, _, second_eq⟩ := Finset.mem_map.mp inRight
  exact contextUnion_positions_ne left right disjoint first second (first_eq.trans second_eq.symm)

private lemma right_not_left (index : Fin right.systemCount) :
    rightPosition left right disjoint index ∉ (leftPlacement left right disjoint).selection := by
  intro member
  obtain ⟨first, _, equal⟩ := Finset.mem_map.mp member
  exact contextUnion_positions_ne left right disjoint first index equal

private def rightComplement (index : Fin right.systemCount) :
    QuantumLayout.SelectedPosition (leftPlacement left right disjoint).selectionᶜ :=
  ⟨rightPosition left right disjoint index,
    Finset.mem_compl.mpr (right_not_left left right disjoint index)⟩

private lemma selected_basis
    (value : (left.disjointUnion right disjoint).register.Index) :
    ((leftPlacement left right disjoint).splitBasis value).1 =
      (unionBasisEquiv left right disjoint value).1 := by
  funext index
  apply Fin.ext
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (leftPlacement left right disjoint) value index).trans
      (contextUnion_split_left_value left right disjoint value index)

private lemma complement_eq_iff
    (row column : (left.disjointUnion right disjoint).register.Index) :
    ((leftPlacement left right disjoint).splitBasis row).2 =
        ((leftPlacement left right disjoint).splitBasis column).2 ↔
      (unionBasisEquiv left right disjoint row).2 =
        (unionBasisEquiv left right disjoint column).2 := by
  constructor
  · intro equal
    funext index
    apply Fin.ext
    have value := congrArg Fin.val (congrFun equal (rightComplement left right disjoint index))
    exact (contextUnion_split_right_value left right disjoint row index).symm.trans
      (value.trans (contextUnion_split_right_value left right disjoint column index))
  · intro equal
    funext index
    apply Fin.ext
    obtain ⟨position, position_eq⟩ := (unionPositionEquiv left right disjoint).surjective index.val
    cases position with
    | inl first =>
        have absent := Finset.mem_compl.mp index.property
        exact False.elim (absent
          (position_eq ▸ Finset.mem_map_of_mem _ (Finset.mem_univ first)))
    | inr second =>
        have value := congrArg (fun basis : right.register.Index => (basis second).val) equal
        change (row index.val).val = (column index.val).val
        rw [← position_eq]
        exact (contextUnion_split_right_value left right disjoint row second).trans
          (value.trans (contextUnion_split_right_value left right disjoint column second).symm)

/-- The original instruction and the real identity frame, on their exact union basis. -/
public def frameUnitary :
    UnitaryCircuit gates oracles (RuntimeCtx.disjointUnion left right disjoint).quantumLayout :=
  UnitaryCircuit.parallel program (UnitaryCircuit.identity gates oracles right.quantumLayout)
    (leftPlacement left right disjoint) (rightPlacement left right disjoint)
    (placements_disjoint left right disjoint)

private lemma frameUnitary_matrix :
    ((frameUnitary left right disjoint program).matrix environment) =
      (leftPlacement left right disjoint).liftOperator (program.matrix environment) := by
  change (rightPlacement left right disjoint).liftOperator 1 *
    (leftPlacement left right disjoint).liftOperator (program.matrix environment) = _
  rw [QuantumLayout.Embedding.embedding_liftOperator_one, one_mul]

/-- Every matrix entry contains the unchanged identity on the full right-context basis. -/
public lemma contextUnion_frameUnitary_entry
    (row column : (RuntimeCtx.disjointUnion left right disjoint).register.Index) :
    ((frameUnitary left right disjoint program).matrix environment) row column =
      (program.matrix environment) (unionBasisEquiv left right disjoint row).1
        (unionBasisEquiv left right disjoint column).1 *
          (if (unionBasisEquiv left right disjoint row).2 =
            (unionBasisEquiv left right disjoint column).2 then 1 else 0) := by
  rw [frameUnitary_matrix, QuantumLayout.Embedding.liftOperator_entry,
    selected_basis, selected_basis]
  simp only [complement_eq_iff]

private lemma selected_basis_right
    (value : (left.disjointUnion right disjoint).register.Index) :
    ((rightPlacement left right disjoint).splitBasis value).1 =
      (unionBasisEquiv left right disjoint value).2 := by
  funext index
  apply Fin.ext
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (rightPlacement left right disjoint) value index).trans
      (contextUnion_split_right_value left right disjoint value index)

private def leftComplement (index : Fin left.systemCount) :
    QuantumLayout.SelectedPosition (rightPlacement left right disjoint).selectionᶜ :=
  ⟨leftPosition left right disjoint index, Finset.mem_compl.mpr (by
    intro member
    obtain ⟨second, _, equal⟩ := Finset.mem_map.mp member
    exact contextUnion_positions_ne left right disjoint index second equal.symm)⟩

private lemma complement_eq_iff_right
    (row column : (left.disjointUnion right disjoint).register.Index) :
    ((rightPlacement left right disjoint).splitBasis row).2 =
        ((rightPlacement left right disjoint).splitBasis column).2 ↔
      (unionBasisEquiv left right disjoint row).1 =
        (unionBasisEquiv left right disjoint column).1 := by
  constructor
  · intro equal
    funext index
    apply Fin.ext
    have value := congrArg Fin.val (congrFun equal (leftComplement left right disjoint index))
    exact (contextUnion_split_left_value left right disjoint row index).symm.trans
      (value.trans (contextUnion_split_left_value left right disjoint column index))
  · intro equal
    funext index
    apply Fin.ext
    obtain ⟨position, position_eq⟩ := (unionPositionEquiv left right disjoint).surjective index.val
    cases position with
    | inl first =>
        have value := congrArg (fun basis : left.register.Index => (basis first).val) equal
        change (row index.val).val = (column index.val).val
        rw [← position_eq]
        exact (contextUnion_split_left_value left right disjoint row first).trans
          (value.trans (contextUnion_split_left_value left right disjoint column first).symm)
    | inr second =>
        have absent := Finset.mem_compl.mp index.property
        exact False.elim (absent
          (position_eq ▸ Finset.mem_map_of_mem _ (Finset.mem_univ second)))

/-- Frame an actual right-context instruction with identity on every left wire. -/
public def frameRightUnitary
    (rightProgram : UnitaryCircuit gates oracles right.quantumLayout) :
    UnitaryCircuit gates oracles (left.disjointUnion right disjoint).quantumLayout :=
  UnitaryCircuit.parallel (UnitaryCircuit.identity gates oracles left.quantumLayout)
    rightProgram (leftPlacement left right disjoint) (rightPlacement left right disjoint)
    (placements_disjoint left right disjoint)

/-- The right instruction acts on exactly the right union basis and fixes the left basis. -/
public lemma contextUnion_frameRightUnitary_entry
    (rightProgram : UnitaryCircuit gates oracles right.quantumLayout)
    (row column : (left.disjointUnion right disjoint).register.Index) :
    ((frameRightUnitary left right disjoint rightProgram).matrix environment) row column =
      (if (unionBasisEquiv left right disjoint row).1 =
        (unionBasisEquiv left right disjoint column).1 then 1 else 0) *
        (rightProgram.matrix environment) (unionBasisEquiv left right disjoint row).2
          (unionBasisEquiv left right disjoint column).2 := by
  have matrix : ((frameRightUnitary left right disjoint rightProgram).matrix environment) =
      (rightPlacement left right disjoint).liftOperator (rightProgram.matrix environment) := by
    change (rightPlacement left right disjoint).liftOperator (rightProgram.matrix environment) *
      (leftPlacement left right disjoint).liftOperator 1 = _
    rw [QuantumLayout.Embedding.embedding_liftOperator_one, mul_one]
  rw [matrix, QuantumLayout.Embedding.liftOperator_entry,
    selected_basis_right, selected_basis_right]
  simp only [complement_eq_iff_right]
  split_ifs <;> ring

/-- Identity framing adds no native or query occurrence. -/
public lemma contextUnion_frameRightUnitary_eventTrace
    (rightProgram : UnitaryCircuit gates oracles right.quantumLayout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (frameRightUnitary left right disjoint rightProgram).eventTrace operations services =
      rightProgram.eventTrace operations services := by
  exact List.nil_append _

/-- Identity framing retains every resource coordinate of the right instruction. -/
public lemma contextUnion_frameRightUnitary_eventCost
    (rightProgram : UnitaryCircuit gates oracles right.quantumLayout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (frameRightUnitary left right disjoint rightProgram).eventCost operations services =
      rightProgram.eventCost operations services := by
  exact zero_add _

/-- Identity framing leaves the right instruction's evaluated depth unchanged. -/
public lemma contextUnion_frameRightUnitary_evaluatedEventDepth
    (rightProgram : UnitaryCircuit gates oracles right.quantumLayout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (weight : Resource.Event (.quantum gates oracles operations services) → Nat) :
    DepthExpr.depthEval weight
      ((frameRightUnitary left right disjoint rightProgram).eventDepth operations services) =
    DepthExpr.depthEval weight (rightProgram.eventDepth operations services) := by
  change max 0 (DepthExpr.depthEval weight
    (rightProgram.eventDepth operations services)) = _
  exact Nat.zero_max _

/-- The actual parallel identity adds no native or query event to the original trace. -/
lemma contextUnion_frameUnitary_eventTrace
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (frameUnitary left right disjoint program).eventTrace operations services =
      program.eventTrace operations services :=
  List.append_nil _

/-- Every native resource coordinate has exactly its original multiplicity. -/
public lemma contextUnion_frameUnitary_eventCost
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (frameUnitary left right disjoint program).eventCost operations services =
      program.eventCost operations services :=
  add_zero _

/-- The symbolic tree records the actual parallel identity factor. -/
public lemma contextUnion_frameUnitary_eventDepth
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (frameUnitary left right disjoint program).eventDepth operations services =
      .tensor (program.eventDepth operations services) .id := by
  rfl

/-- The true framed instruction has the original depth for every event duration assignment. -/
public lemma contextUnion_frameUnitary_evaluatedEventDepth
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (weight : Resource.Event (.quantum gates oracles operations services) → Nat) :
    DepthExpr.depthEval weight ((frameUnitary left right disjoint program).eventDepth
      operations services) =
        DepthExpr.depthEval weight (program.eventDepth operations services) := by
  simp only [contextUnion_frameUnitary_eventDepth,
    DepthExpr.depthEval, Nat.max_zero]

/-- The real right frame and an arbitrary external reference retain their matrix coordinates. -/
public lemma contextUnion_frameUnitary_reference_entry {Reference : Register}
    (row column : (RuntimeCtx.disjointUnion left right disjoint).register.Index)
    (refRow refColumn : Reference.Index) :
    (UnitaryOperator.prodTensor ((frameUnitary left right disjoint program).matrix environment)
      (1 : UnitaryOperator Reference)) (row, refRow) (column, refColumn) =
        ((program.matrix environment) (unionBasisEquiv left right disjoint row).1
          (unionBasisEquiv left right disjoint column).1 *
            (if (unionBasisEquiv left right disjoint row).2 =
              (unionBasisEquiv left right disjoint column).2 then 1 else 0)) *
                (if refRow = refColumn then 1 else 0) := by
  rw [UnitaryOperator.prodTensor_apply, contextUnion_frameUnitary_entry]
  rfl

end

end QuantumAlg.Execution.ContextUnion
