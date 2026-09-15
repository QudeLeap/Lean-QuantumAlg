/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Target.Centering.Readout

/-!
# Exact values of the actual centered-target decisions

The equality tests the real initial scratch value, while the later strict
comparison tests the actual half-modulus copy. The enclosing native layout
supplies the required reference positions. These equations themselves allow
an arbitrary initial scratch word; actual zero allocation is connected only
when identifying the source's zero test.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual three cells written by the unconditional decision prefix. -/
def decisionKeys (refs : Refs ctx width) : List StorageKey :=
  [refs.isZero.key, refs.scratch.key, refs.belowHalf.key]

/-- Internal placement facts of the actual prefix, to be discharged by its enclosing layout. -/
structure DecisionSeparated (refs : Refs ctx width) : Prop where
  /-- The three actual destinations are distinct storage cells. -/
  unique : (decisionKeys refs).Nodup
  /-- All source preimage reads survive the decision prefix. -/
  preimage : ∀ key ∈ decisionKeys refs, key ∉ refs.preimage.storageKeys
  /-- The original modulus survives the decision prefix. -/
  modulus : ∀ key ∈ decisionKeys refs, key ∉ refs.modulus.storageKeys

private theorem decision_key_ne (refs : Refs ctx width) (separated : DecisionSeparated refs)
    (left right : Fin 3) (different : left ≠ right) :
    (decisionKeys refs).get ⟨left.val, by change left.val < 3; exact left.isLt⟩ ≠
      (decisionKeys refs).get ⟨right.val, by change right.val < 3; exact right.isLt⟩ := by
  intro same
  have positions := separated.unique.injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- Actual operands keep their original complete word values through all prefix instructions. -/
theorem nativeLattice_targetCentering_decision_sources (refs : Refs ctx width)
    (separated : DecisionSeparated refs) (store : Store ctx) :
    (decisionStore refs store).read refs.preimage = store.read refs.preimage ∧
      (decisionStore refs store).read refs.modulus = store.read refs.modulus := by
  exact ⟨nativeLattice_targetCentering_decision_read_other refs refs.preimage
    (separated.preimage _ (by simp [decisionKeys]))
    (separated.preimage _ (by simp [decisionKeys]))
    (separated.preimage _ (by simp [decisionKeys])) store,
    nativeLattice_targetCentering_decision_read_other refs refs.modulus
      (separated.modulus _ (by simp [decisionKeys]))
      (separated.modulus _ (by simp [decisionKeys]))
      (separated.modulus _ (by simp [decisionKeys])) store⟩

/-- The three actual prefix values depend only on the incoming source and scratch words. -/
theorem nativeLattice_targetCentering_decision_values (refs : Refs ctx width)
    (separated : DecisionSeparated refs) (store : Store ctx) :
    ((decisionStore refs store).read (.storage refs.scratch.toCStorageRef)).toNat =
        (store.read refs.modulus).toNat / 2 ∧
      ((decisionStore refs store).read (.storage refs.isZero.toCStorageRef)).toBool =
        decide ((store.read refs.preimage).toNat =
          (store.read (.storage refs.scratch.toCStorageRef)).toNat) ∧
      ((decisionStore refs store).read (.storage refs.belowHalf.toCStorageRef)).toBool =
        decide ((store.read refs.preimage).toNat < (store.read refs.modulus).toNat / 2) := by
  let equalized := store.applyOp (equalOp refs)
  let copied := equalized.applyOp (copyOp refs)
  let halved := copied.applyOp (halfOp refs)
  have scratchZero : refs.scratch.key ≠ refs.isZero.key :=
    decision_key_ne refs separated 1 0 (by decide)
  have belowZero : refs.belowHalf.key ≠ refs.isZero.key :=
    decision_key_ne refs separated 2 0 (by decide)
  have belowScratch : refs.belowHalf.key ≠ refs.scratch.key :=
    decision_key_ne refs separated 2 1 (by decide)
  have preimageZero : refs.isZero.key ∉ refs.preimage.storageKeys :=
    separated.preimage _ (by simp [decisionKeys])
  have preimageScratch : refs.scratch.key ∉ refs.preimage.storageKeys :=
    separated.preimage _ (by simp [decisionKeys])
  have modulusZero : refs.isZero.key ∉ refs.modulus.storageKeys :=
    separated.modulus _ (by simp [decisionKeys])
  have modulusRead : equalized.read refs.modulus = store.read refs.modulus :=
    Store.read_applyOp_of_not_mem_storageKeys store (equalOp refs) refs.modulus modulusZero
  have copyRead : copied.read (.storage refs.scratch.toCStorageRef) = store.read refs.modulus :=
    (Store.read_applyOp_output equalized (copyOp refs)).trans modulusRead
  have halfRaw : (halved.read (.storage refs.scratch.toCStorageRef)).toNat =
      ((copied.read (.storage refs.scratch.toCStorageRef)).toNat / 2) % 2 ^ width :=
    congrArg CShape.Value.toNat (Store.read_applyOp_output copied (halfOp refs))
  have halfValue : (halved.read (.storage refs.scratch.toCStorageRef)).toNat =
      (store.read refs.modulus).toNat / 2 :=
    halfRaw.trans ((congrArg (fun value : CShape.Word width => (value.toNat / 2) % 2 ^ width)
      copyRead).trans (Nat.mod_eq_of_lt
        ((Nat.div_le_self _ _).trans_lt (store.read refs.modulus).toNat_lt)))
  have preimageRead : halved.read refs.preimage = store.read refs.preimage :=
    (Store.read_applyOp_of_not_mem_storageKeys copied (halfOp refs)
      refs.preimage preimageScratch).trans
      ((Store.read_applyOp_of_not_mem_storageKeys equalized (copyOp refs)
        refs.preimage preimageScratch).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (equalOp refs)
          refs.preimage preimageZero))
  have zeroValue : (equalized.read (.storage refs.isZero.toCStorageRef)).toBool =
      decide ((store.read refs.preimage).toNat =
        (store.read (.storage refs.scratch.toCStorageRef)).toNat) :=
    congrArg CShape.Value.toBool (Store.read_applyOp_output store (equalOp refs))
  have zeroPreserved : (decisionStore refs store).read (.storage refs.isZero.toCStorageRef) =
      equalized.read (.storage refs.isZero.toCStorageRef) :=
    (Store.read_applyOp_of_not_mem_storageKeys halved (lessOp refs)
      (.storage refs.isZero.toCStorageRef)
      (fun member => belowZero (List.mem_singleton.mp member))).trans
      ((Store.read_applyOp_of_not_mem_storageKeys copied (halfOp refs)
        (.storage refs.isZero.toCStorageRef)
        (fun member => scratchZero (List.mem_singleton.mp member))).trans
        (Store.read_applyOp_of_not_mem_storageKeys equalized (copyOp refs)
          (.storage refs.isZero.toCStorageRef)
          (fun member => scratchZero (List.mem_singleton.mp member))))
  have scratchPreserved : (decisionStore refs store).read (.storage refs.scratch.toCStorageRef) =
      halved.read (.storage refs.scratch.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys halved (lessOp refs)
      (.storage refs.scratch.toCStorageRef)
      (fun member => belowScratch (List.mem_singleton.mp member))
  have compared : ((decisionStore refs store).read (.storage refs.belowHalf.toCStorageRef)).toBool =
      decide ((halved.read refs.preimage).toNat <
        (halved.read (.storage refs.scratch.toCStorageRef)).toNat) :=
    congrArg CShape.Value.toBool (Store.read_applyOp_output halved (lessOp refs))
  exact ⟨(congrArg CShape.Value.toNat scratchPreserved).trans halfValue,
    (congrArg CShape.Value.toBool zeroPreserved).trans zeroValue,
    compared.trans (congrArg₂ (fun left right : Nat => decide (left < right))
      (congrArg CShape.Value.toNat preimageRead) halfValue)⟩

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering
