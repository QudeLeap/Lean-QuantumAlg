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

variable (left right : RuntimeCtx .quantum)
  (disjoint : RuntimeCtx.StorageDisjoint left right)
  (program : UnitaryCircuit left.register) (placed : program.physical_idx = left.physicalIdx)

private def frameIdentity : UnitaryCircuit right.register :=
  UnitaryCircuit.identity right.register right.physicalIdx right.identitiesNodup

include disjoint placed in
private theorem frameMerge :
    PhysicalLayout.DisjointMerge program.physical_idx (frameIdentity right).physical_idx := by
  refine ⟨program.physical_idx_nodup, right.identitiesNodup, ?_⟩
  change List.Disjoint program.physical_idx right.physicalIdx
  rw [placed]
  exact (RuntimeCtx.physicallyDisjoint_iff_listDisjoint left right).mp disjoint.2

/-- The original instruction and the real identity frame, on their exact union basis. -/
public def frameUnitary :
    UnitaryCircuit (RuntimeCtx.disjointUnion left right disjoint).register :=
  UnitaryCircuit.reindex (unionBasisEquiv left right disjoint).symm
    (UnitaryCircuit.tensor program (frameIdentity right)
      (frameMerge left right disjoint program placed))

/-- The placed instruction advertises every actual union wire in the correct order. -/
public theorem contextUnion_frameUnitary_physical :
    (frameUnitary left right disjoint program placed).physical_idx =
      (RuntimeCtx.disjointUnion left right disjoint).physicalIdx := by
  change program.physical_idx ++ right.physicalIdx = _
  rw [placed, RuntimeCtx.physicalIdx_disjointUnion]

private theorem frameUnitary_matrix :
    (frameUnitary left right disjoint program placed).matrix =
      UnitaryOperator.reindex (unionBasisEquiv left right disjoint).symm
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator right.register)) := by
  rfl

/-- Every matrix entry contains the unchanged identity on the full right-context basis. -/
public theorem contextUnion_frameUnitary_entry
    (row column : (RuntimeCtx.disjointUnion left right disjoint).register.Index) :
    (frameUnitary left right disjoint program placed).matrix row column =
      program.matrix (unionBasisEquiv left right disjoint row).1
        (unionBasisEquiv left right disjoint column).1 *
          (if (unionBasisEquiv left right disjoint row).2 =
            (unionBasisEquiv left right disjoint column).2 then 1 else 0) := by
  rw [frameUnitary_matrix]
  change (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator right.register))
    (unionBasisEquiv left right disjoint row)
    (unionBasisEquiv left right disjoint column) = _
  rw [UnitaryOperator.prodTensor_apply]
  rfl

/-- Literal tensor/reindex syntax adds no native event to the original ordered trace. -/
theorem contextUnion_frameUnitary_eventTrace :
    (frameUnitary left right disjoint program placed).eventTrace = program.eventTrace := by
  change program.eventTrace ++ (frameIdentity right).eventTrace = program.eventTrace
  exact (congrArg (List.append program.eventTrace)
    (UnitaryCircuit.identity_eventTrace right.register right.physicalIdx
      right.identitiesNodup)).trans
      (List.append_nil program.eventTrace)

/-- Every native resource coordinate has exactly its original multiplicity. -/
public theorem contextUnion_frameUnitary_eventCost :
    (frameUnitary left right disjoint program placed).eventCost = program.eventCost := by
  change program.eventCost + (frameIdentity right).eventCost = program.eventCost
  exact (congrArg (fun cost => program.eventCost + cost)
    (UnitaryCircuit.identity_eventCost right.register right.physicalIdx
      right.identitiesNodup)).trans
      (add_zero program.eventCost)

/-- The symbolic tree records the actual parallel identity factor. -/
public theorem contextUnion_frameUnitary_eventDepth :
    (frameUnitary left right disjoint program placed).eventDepth =
      .tensor program.eventDepth .id := by
  change DepthExpr.tensor program.eventDepth (frameIdentity right).eventDepth =
    DepthExpr.tensor program.eventDepth .id
  exact congrArg (DepthExpr.tensor program.eventDepth)
    (UnitaryCircuit.identity_eventDepth right.register right.physicalIdx right.identitiesNodup)

/-- The true framed instruction has the original depth for every event duration assignment. -/
public theorem contextUnion_frameUnitary_evaluatedEventDepth
    (weight : Resource.Event .quantum → Nat) :
    (frameUnitary left right disjoint program placed).evaluatedEventDepth weight =
      program.evaluatedEventDepth weight := by
  simp only [UnitaryCircuit.evaluatedEventDepth, contextUnion_frameUnitary_eventDepth,
    DepthExpr.depthEval, Nat.max_zero]

/-- The real right frame and an arbitrary external reference retain their matrix coordinates. -/
public theorem contextUnion_frameUnitary_reference_entry {Reference : Register}
    (row column : (RuntimeCtx.disjointUnion left right disjoint).register.Index)
    (refRow refColumn : Reference.Index) :
    (UnitaryOperator.prodTensor (frameUnitary left right disjoint program placed).matrix
      (1 : UnitaryOperator Reference)) (row, refRow) (column, refColumn) =
        (program.matrix (unionBasisEquiv left right disjoint row).1
          (unionBasisEquiv left right disjoint column).1 *
            (if (unionBasisEquiv left right disjoint row).2 =
              (unionBasisEquiv left right disjoint column).2 then 1 else 0)) *
                (if refRow = refColumn then 1 else 0) := by
  rw [UnitaryOperator.prodTensor_apply, contextUnion_frameUnitary_entry]
  rfl

end

end QuantumAlg.Execution.ContextUnion
