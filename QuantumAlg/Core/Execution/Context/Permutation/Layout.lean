/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Context
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.Perm.Basic

/-!
# Identical physical systems under an entry permutation

The position correspondence is derived from equality of complete wire records,
including physical identity and positive dimension. Each computational-basis
value stays on its original wire. Resident and auxiliary counts are unchanged
because all complete entries and their storage roles remain present.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {kind : ProblemKind} {source target : RuntimeCtx kind}
  (same : source.entries.Perm target.entries)

include same in
/-- Every complete wire record survives, with only its list position changed. -/
lemma quantumWires_perm : source.quantumWires.Perm target.quantumWires :=
  List.Perm.flatMap_right RuntimeEntry.quantumWires same

include same in
private lemma position_exists (index : Fin source.systemCount) :
    ∃ moved : Fin target.systemCount,
      target.quantumLayout.wire moved = source.quantumLayout.wire index := by
  have present : source.quantumLayout.wire index ∈ source.quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have relocated := (quantumWires_perm same).mem_iff.mp present
  rw [← RuntimeCtx.quantumLayout_wires, QuantumLayout.wires, List.mem_ofFn] at relocated
  exact relocated

private def position (index : Fin source.systemCount) : Fin target.systemCount :=
  (position_exists same index).choose

private lemma position_wire (index : Fin source.systemCount) :
    target.quantumLayout.wire (position same index) = source.quantumLayout.wire index :=
  (position_exists same index).choose_spec

/-- Physical identity determines the unique corresponding position in the target context. -/
def positions : Fin source.systemCount ≃ Fin target.systemCount where
  toFun := position same
  invFun := position same.symm
  left_inv index := source.quantumLayout.position_eq_of_identity_eq
    (congrArg QuantumWire.identity
      ((position_wire same.symm (position same index)).trans (position_wire same index)))
  right_inv index := target.quantumLayout.position_eq_of_identity_eq
    (congrArg QuantumWire.identity
      ((position_wire same (position same.symm index)).trans (position_wire same.symm index)))

/-- The correspondence preserves physical identity and dimension together. -/
lemma positions_wire (index : Fin source.systemCount) :
    target.quantumLayout.wire (positions same index) = source.quantumLayout.wire index :=
  position_wire same index

/-- Re-express the same wire values in the corresponding dependent-product basis. -/
def basis : source.register.Index ≃ target.register.Index :=
  (positions same).piCongr fun index =>
    finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
      (positions_wire same index).symm)

/-- Each basis value remains numerically unchanged on the identical physical system. -/
lemma basis_value (value : source.register.Index) (index : Fin source.systemCount) :
    (basis same value (positions same index)).val = (value index).val := by
  exact congrArg
    (fun result : Fin (target.quantumLayout.wire (positions same index)).dimension => result.val)
    (Equiv.piCongr_apply_apply
      (W := fun position : Fin source.systemCount =>
        Fin (source.quantumLayout.wire position).dimension)
      (Z := fun position : Fin target.systemCount =>
        Fin (target.quantumLayout.wire position).dimension)
      (positions same)
      (fun position : Fin source.systemCount =>
        finCongr (congrArg (fun wire : QuantumWire => (wire.dimension : Nat))
          (positions_wire same position).symm)) value index)

private lemma fold_space_perm {entries reordered : List (RuntimeEntry kind)}
    (permuted : entries.Perm reordered) (project : RuntimeEntry kind → SpacePool kind) :
    entries.foldr (fun entry total => project entry + total) 0 =
      reordered.foldr (fun entry total => project entry + total) 0 := by
  induction permuted with
  | nil => rfl
  | cons entry _ ih => simpa only [List.foldr_cons] using congrArg (project entry + ·) ih
  | swap first second tail =>
      simp only [List.foldr_cons]
      funext axis
      exact Nat.add_left_comm _ _ _
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH

include same in
/-- Every original resident classical bit and dimension-indexed quantum system stays counted. -/
lemma resident_space : source.residentSpace = target.residentSpace :=
  fold_space_perm same RuntimeEntry.residentSpace

include same in
/-- The identical original storage roles give the identical auxiliary-space coordinates. -/
lemma auxiliary_space : source.auxiliarySpace = target.auxiliarySpace :=
  fold_space_perm same RuntimeEntry.auxiliarySpace

end

end QuantumAlg.Execution.ContextPermutation
