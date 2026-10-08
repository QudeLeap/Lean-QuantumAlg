/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Base.Layout.Quantum.Append
public import Mathlib.Logic.Equiv.Basic

/-!
# Exact layouts after adding owned physical systems

Adding an owned layout places its actual wire records before every existing
context wire. The bridge below starts from equality of these complete ordered
wire lists. Corresponding positions therefore retain both physical identity
and local dimension, and their finite basis values are transported unchanged.

This identifies the concrete tensor coordinates [dW19, qcnotes.tex:389] with
the live context register. It does not infer a physical correspondence from
the dimension of a Hilbert space alone.
-/

section

namespace QuantumAlg

namespace Execution

/-- Coordinate equivalence induced by equality of complete ordered wire lists. -/
public def positionsOfEqualWires {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (sameWires : left.wires = right.wires) : Fin leftCount ≃ Fin rightCount :=
  finCongr (by simpa only [QuantumLayout.wires_length] using congrArg List.length sameWires)

public theorem wireAtCorrespondingPosition {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (sameWires : left.wires = right.wires) (index : Fin leftCount) :
    right.wire (positionsOfEqualWires left right sameWires index) = left.wire index := by
  have sameEntry := congrArg (fun wires : List QuantumWire => wires[index.val]?) sameWires
  have leftEntry : left.wires[index.val]? = some (left.wire index) := by
    simp [QuantumLayout.wires]
  have rightEntry : right.wires[index.val]? =
      some (right.wire (positionsOfEqualWires left right sameWires index)) := by
    change (List.ofFn right.wire)[(positionsOfEqualWires left right sameWires index).val]? = _
    simp
  exact (Option.some.inj (leftEntry.symm.trans (sameEntry.trans rightEntry))).symm

/-- Basis equivalence induced by equality of complete ordered wire lists. -/
public def basisOfEqualWires {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (sameWires : left.wires = right.wires) : left.Basis ≃ right.Basis :=
  (positionsOfEqualWires left right sameWires).piCongr fun index =>
    finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
      (wireAtCorrespondingPosition left right sameWires index).symm)

public theorem basisOfEqualWires_value {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (sameWires : left.wires = right.wires) (basis : left.Basis) (index : Fin leftCount) :
    (basisOfEqualWires left right sameWires basis
      (positionsOfEqualWires left right sameWires index)).val = (basis index).val := by
  exact congrArg
    (fun value : Fin (right.wire (positionsOfEqualWires left right sameWires index)).dimension =>
      value.val)
    (Equiv.piCongr_apply_apply
      (W := fun position : Fin leftCount => Fin (left.wire position).dimension)
      (Z := fun position : Fin rightCount => Fin (right.wire position).dimension)
      (positionsOfEqualWires left right sameWires)
      (fun position : Fin leftCount =>
        finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
          (wireAtCorrespondingPosition left right sameWires position).symm)) basis index)

end Execution

namespace RuntimeCtx

variable {systemCount : Nat}

/-- The context's layout and physical-identity list certify the same disjointness. -/
theorem addOwnedLayout_layoutDisjoint (ctx : RuntimeCtx .quantum)
    (layout : QuantumLayout systemCount)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    List.Disjoint layout.identities ctx.quantumLayout.identities := by
  simpa only [RuntimeCtx.runtimeCtx_quantumLayout_identities] using disjoint

/-- Head preparation and context extension contain the same ordered wire records. -/
theorem addOwnedLayout_wires_eq_append (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (QuantumLayout.append layout ctx.quantumLayout
      (addOwnedLayout_layoutDisjoint ctx layout disjoint)).wires =
        (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wires := by
  calc
    _ = layout.wires ++ ctx.quantumLayout.wires :=
      QuantumLayout.wires_append layout ctx.quantumLayout _
    _ = layout.wires ++ ctx.quantumWires := by
      rw [RuntimeCtx.quantumLayout_wires]
    _ = (ctx.addOwnedLayout key layout fresh disjoint).quantumWires :=
      (RuntimeCtx.runtimeCtx_quantumWires_addOwnedLayout
        ctx key layout fresh disjoint).symm
    _ = _ := (RuntimeCtx.quantumLayout_wires _).symm

/-- Corresponding positions follow the equality of the actual ordered wire lists. -/
def addOwnedLayoutPositionEquiv (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    Fin (systemCount + ctx.systemCount) ≃
      Fin (ctx.addOwnedLayout key layout fresh disjoint).systemCount :=
  Execution.positionsOfEqualWires _ _ (addOwnedLayout_wires_eq_append ctx key layout fresh disjoint)

/-- Corresponding positions preserve the whole physical wire, including identity and dimension. -/
theorem addOwnedLayout_wire_preserved (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (index : Fin (systemCount + ctx.systemCount)) :
    (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
      (addOwnedLayoutPositionEquiv ctx key layout fresh disjoint index) =
        (QuantumLayout.append layout ctx.quantumLayout
          (addOwnedLayout_layoutDisjoint ctx layout disjoint)).wire index :=
  Execution.wireAtCorrespondingPosition _ _
    (addOwnedLayout_wires_eq_append ctx key layout fresh disjoint) index

/-- Every corresponding physical position retains its precise finite dimension. -/
theorem addOwnedLayout_dimension_preserved (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (index : Fin (systemCount + ctx.systemCount)) :
    ((ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
      (addOwnedLayoutPositionEquiv ctx key layout fresh disjoint index)).dimension =
        ((QuantumLayout.append layout ctx.quantumLayout
          (addOwnedLayout_layoutDisjoint ctx layout disjoint)).wire index).dimension :=
  congrArg QuantumWire.dimension
    (addOwnedLayout_wire_preserved ctx key layout fresh disjoint index)

/-- Convert head-preparation tensor labels to the exact new live context basis. -/
def addOwnedLayoutBasisEquiv (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (QuantumLayout.append layout ctx.quantumLayout
      (addOwnedLayout_layoutDisjoint ctx layout disjoint)).Basis ≃
        (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.Basis :=
  Execution.basisOfEqualWires _ _ (addOwnedLayout_wires_eq_append ctx key layout fresh disjoint)

/-- Transport retains the finite value at every corresponding physical position. -/
theorem addOwnedLayout_basis_value_preserved (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (basis : (QuantumLayout.append layout ctx.quantumLayout
      (addOwnedLayout_layoutDisjoint ctx layout disjoint)).Basis)
    (index : Fin (systemCount + ctx.systemCount)) :
    (addOwnedLayoutBasisEquiv ctx key layout fresh disjoint basis
      (addOwnedLayoutPositionEquiv ctx key layout fresh disjoint index)).val = (basis index).val :=
  Execution.basisOfEqualWires_value _ _
    (addOwnedLayout_wires_eq_append ctx key layout fresh disjoint) basis index

end RuntimeCtx

end QuantumAlg

end
