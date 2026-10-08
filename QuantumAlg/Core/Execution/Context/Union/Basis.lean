/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Execution.Context.Layout
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact quantum coordinates of disjoint runtime contexts

The runtime union appends the actual ordered wire records. Its tensor basis
is therefore obtained from those positions, retaining each physical identity,
local dimension and finite value. This realizes the tensor basis
[dW19, qcnotes.tex:389] for arbitrary qudits and keeps both contexts resident.
-/

namespace QuantumAlg.Execution.ContextUnion

section

variable {kind : ProblemKind} (left right : RuntimeCtx kind)
  (disjoint : RuntimeCtx.StorageDisjoint left right)

include disjoint in
private theorem layoutDisjoint :
    List.Disjoint left.quantumLayout.identities right.quantumLayout.identities := by
  simpa only [RuntimeCtx.runtimeCtx_quantumLayout_identities] using
    (RuntimeCtx.physicallyDisjoint_iff_listDisjoint left right).mp
      (RuntimeCtx.physicallyDisjoint_of_storageDisjoint disjoint)

private theorem appendWires :
    (QuantumLayout.append left.quantumLayout right.quantumLayout
      (layoutDisjoint left right disjoint)).wires =
        (RuntimeCtx.disjointUnion left right disjoint).quantumLayout.wires := by
  simp only [QuantumLayout.wires_append, RuntimeCtx.quantumLayout_wires,
    RuntimeCtx.quantumWires_disjointUnion]

private def appendPositionEquiv : Fin (left.systemCount + right.systemCount) ≃
    Fin (RuntimeCtx.disjointUnion left right disjoint).systemCount :=
  positionsOfEqualWires _ _ (appendWires left right disjoint)

/-- Actual union positions, with the left segment followed by the right segment. -/
public def unionPositionEquiv : Fin left.systemCount ⊕ Fin right.systemCount ≃
    Fin (RuntimeCtx.disjointUnion left right disjoint).systemCount :=
  finSumFinEquiv.trans (appendPositionEquiv left right disjoint)

/-- The unchanged physical position of a left-context wire in the union. -/
public def leftPosition (index : Fin left.systemCount) :
    Fin (RuntimeCtx.disjointUnion left right disjoint).systemCount :=
  unionPositionEquiv left right disjoint (.inl index)

/-- The physical position of a right-context wire after the left segment. -/
public def rightPosition (index : Fin right.systemCount) :
    Fin (RuntimeCtx.disjointUnion left right disjoint).systemCount :=
  unionPositionEquiv left right disjoint (.inr index)

/-- Appending a context does not change a left wire's numerical position. -/
public theorem contextUnion_leftPosition_val (index : Fin left.systemCount) :
    (leftPosition left right disjoint index).val = index.val := by
  rfl

/-- A right wire is offset by the actual number of left physical systems. -/
public theorem contextUnion_rightPosition_val (index : Fin right.systemCount) :
    (rightPosition left right disjoint index).val = left.systemCount + index.val := by
  rfl

/-- Left positions retain their complete physical wire records. -/
public theorem contextUnion_left_wire (index : Fin left.systemCount) :
    (RuntimeCtx.disjointUnion left right disjoint).quantumLayout.wire
      (leftPosition left right disjoint index) = left.quantumLayout.wire index := by
  calc
    _ = (QuantumLayout.append left.quantumLayout right.quantumLayout
        (layoutDisjoint left right disjoint)).wire (Fin.castAdd right.systemCount index) :=
      wireAtCorrespondingPosition _ _ (appendWires left right disjoint)
        (Fin.castAdd right.systemCount index)
    _ = _ := by simp only [QuantumLayout.append, Fin.append_left]

/-- Right positions retain their complete physical wire records. -/
public theorem contextUnion_right_wire (index : Fin right.systemCount) :
    (RuntimeCtx.disjointUnion left right disjoint).quantumLayout.wire
      (rightPosition left right disjoint index) = right.quantumLayout.wire index := by
  calc
    _ = (QuantumLayout.append left.quantumLayout right.quantumLayout
        (layoutDisjoint left right disjoint)).wire (Fin.natAdd left.systemCount index) :=
      wireAtCorrespondingPosition _ _ (appendWires left right disjoint)
        (Fin.natAdd left.systemCount index)
    _ = _ := by simp only [QuantumLayout.append, Fin.append_right]

/-- The local dimension of each left wire is unchanged. -/
public theorem contextUnion_left_dimension (index : Fin left.systemCount) :
    ((RuntimeCtx.disjointUnion left right disjoint).quantumLayout.wire
      (leftPosition left right disjoint index)).dimension =
        (left.quantumLayout.wire index).dimension :=
  congrArg QuantumWire.dimension (contextUnion_left_wire left right disjoint index)

/-- The local dimension of each right wire is unchanged. -/
public theorem contextUnion_right_dimension (index : Fin right.systemCount) :
    ((RuntimeCtx.disjointUnion left right disjoint).quantumLayout.wire
      (rightPosition left right disjoint index)).dimension =
        (right.quantumLayout.wire index).dimension :=
  congrArg QuantumWire.dimension (contextUnion_right_wire left right disjoint index)

/-- Distinct sides of a runtime union never designate the same physical position. -/
public theorem contextUnion_positions_ne (leftIndex : Fin left.systemCount)
    (rightIndex : Fin right.systemCount) :
    leftPosition left right disjoint leftIndex ≠ rightPosition left right disjoint rightIndex := by
  intro equal
  have impossible := (unionPositionEquiv left right disjoint).injective equal
  cases impossible

private def appendBasis :
    (QuantumLayout.append left.quantumLayout right.quantumLayout
      (layoutDisjoint left right disjoint)).Basis ≃
        (RuntimeCtx.disjointUnion left right disjoint).register.Index :=
  basisOfEqualWires _ _ (appendWires left right disjoint)

/-- Split the real union basis along its two actual ordered wire segments. -/
public def unionBasisEquiv :
    (RuntimeCtx.disjointUnion left right disjoint).register.Index ≃
      left.register.Index × right.register.Index :=
  (appendBasis left right disjoint).symm.trans
    (QuantumLayout.appendBasisEquiv left.quantumLayout right.quantumLayout
      (layoutDisjoint left right disjoint))

/-- Reassembly places precisely the original finite values on the left wires. -/
public theorem contextUnion_join_left_value (leftBasis : left.register.Index)
    (rightBasis : right.register.Index) (index : Fin left.systemCount) :
    ((unionBasisEquiv left right disjoint).symm (leftBasis, rightBasis)
      (leftPosition left right disjoint index)).val = (leftBasis index).val := by
  let joined := QuantumLayout.appendJoinBasis left.quantumLayout right.quantumLayout
    (layoutDisjoint left right disjoint) leftBasis rightBasis
  have transported := basisOfEqualWires_value _ _ (appendWires left right disjoint)
    joined (Fin.castAdd right.systemCount index)
  exact transported.trans (QuantumLayout.appendJoinBasis_left_value left.quantumLayout
    right.quantumLayout (layoutDisjoint left right disjoint) leftBasis rightBasis index)

/-- Reassembly places precisely the original finite values on the right wires. -/
public theorem contextUnion_join_right_value (leftBasis : left.register.Index)
    (rightBasis : right.register.Index) (index : Fin right.systemCount) :
    ((unionBasisEquiv left right disjoint).symm (leftBasis, rightBasis)
      (rightPosition left right disjoint index)).val = (rightBasis index).val := by
  let joined := QuantumLayout.appendJoinBasis left.quantumLayout right.quantumLayout
    (layoutDisjoint left right disjoint) leftBasis rightBasis
  have transported := basisOfEqualWires_value _ _ (appendWires left right disjoint)
    joined (Fin.natAdd left.systemCount index)
  exact transported.trans (QuantumLayout.appendJoinBasis_right_value left.quantumLayout
    right.quantumLayout (layoutDisjoint left right disjoint) leftBasis rightBasis index)

/-- Splitting reads exactly the finite value at each actual left position. -/
public theorem contextUnion_split_left_value
    (basis : (RuntimeCtx.disjointUnion left right disjoint).register.Index)
    (index : Fin left.systemCount) :
    (basis (leftPosition left right disjoint index)).val =
      ((unionBasisEquiv left right disjoint basis).1 index).val := by
  have roundtrip := congrArg
    (fun label : (RuntimeCtx.disjointUnion left right disjoint).register.Index =>
      (label (leftPosition left right disjoint index)).val)
    ((unionBasisEquiv left right disjoint).symm_apply_apply basis)
  exact roundtrip.symm.trans (contextUnion_join_left_value left right disjoint
    (unionBasisEquiv left right disjoint basis).1
    (unionBasisEquiv left right disjoint basis).2 index)

/-- Splitting reads exactly the finite value at each actual right position. -/
public theorem contextUnion_split_right_value
    (basis : (RuntimeCtx.disjointUnion left right disjoint).register.Index)
    (index : Fin right.systemCount) :
    (basis (rightPosition left right disjoint index)).val =
      ((unionBasisEquiv left right disjoint basis).2 index).val := by
  have roundtrip := congrArg
    (fun label : (RuntimeCtx.disjointUnion left right disjoint).register.Index =>
      (label (rightPosition left right disjoint index)).val)
    ((unionBasisEquiv left right disjoint).symm_apply_apply basis)
  exact roundtrip.symm.trans (contextUnion_join_right_value left right disjoint
    (unionBasisEquiv left right disjoint basis).1
    (unionBasisEquiv left right disjoint basis).2 index)

/-- The left readout is equality in the correctly transported finite carrier. -/
public theorem contextUnion_split_left
    (basis : (RuntimeCtx.disjointUnion left right disjoint).register.Index)
    (index : Fin left.systemCount) :
    Fin.cast (congrArg (fun dim : ℕ+ => (dim : Nat))
      (contextUnion_left_dimension left right disjoint index))
      (basis (leftPosition left right disjoint index)) =
        (unionBasisEquiv left right disjoint basis).1 index := by
  apply Fin.ext
  exact contextUnion_split_left_value left right disjoint basis index

/-- The right readout is equality in the correctly transported finite carrier. -/
public theorem contextUnion_split_right
    (basis : (RuntimeCtx.disjointUnion left right disjoint).register.Index)
    (index : Fin right.systemCount) :
    Fin.cast (congrArg (fun dim : ℕ+ => (dim : Nat))
      (contextUnion_right_dimension left right disjoint index))
      (basis (rightPosition left right disjoint index)) =
        (unionBasisEquiv left right disjoint basis).2 index := by
  apply Fin.ext
  exact contextUnion_split_right_value left right disjoint basis index

end

end QuantumAlg.Execution.ContextUnion
