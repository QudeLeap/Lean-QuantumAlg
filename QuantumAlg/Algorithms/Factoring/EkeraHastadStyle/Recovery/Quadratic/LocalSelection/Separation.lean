/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Selection

/-!
# Internal separation from the actual local scope positions

The original local selector lies below four freshly allocated candidate
words. Their intrinsic keys prove all still-live candidate and latch
separation facts. The fresh checker cells then supply the remaining selector
conditions. No property of caller values or caller storage aliasing is added.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem old_ne_candidate {shape : CShape}
    (output : CWriteRef ctx shape) (key : StorageKey)
    (internal : key ∈ Layout.internalKeys ctx width) :
    (Layout.underWrite output width).key ≠ key := by
  have liftedKey : (Layout.underWrite output width).key = output.key := rfl
  intro same
  have original : output.key ∈ ctx.keys :=
    (CInputRef.storage output.toCStorageRef).storageKeys_subset_context
      (List.mem_singleton.mpr rfl)
  have sameOriginal : output.key = key := liftedKey.symm.trans same
  exact List.disjoint_left.mp (Layout.nativeQuadratic_layout_disjoint ctx width)
    internal (sameOriginal ▸ original)

private theorem candidate_free {shape : CShape}
    (output : CWriteRef (selectionContext ctx width) shape) :
    (Layout.underWrite output width).key ∉
        (CInputRef.storage (arithmeticRefs ctx width).first.toCStorageRef).storageKeys ∧
      (Layout.underWrite output width).key ∉
        (CInputRef.storage (arithmeticRefs ctx width).second.toCStorageRef).storageKeys := by
  constructor
  · exact fun present => old_ne_candidate output (arithmeticRefs ctx width).first.key
      (List.get_mem (Layout.internalKeys (selectionContext ctx width) width)
        ⟨1, by change 1 < 4; decide⟩) (List.mem_singleton.mp present)
  · exact fun present => old_ne_candidate output (arithmeticRefs ctx width).second.key
      (List.get_mem (Layout.internalKeys (selectionContext ctx width) width)
        ⟨0, by change 0 < 4; decide⟩) (List.mem_singleton.mp present)

private def selectorKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 4) : StorageKey :=
  (SelectionLayout.internalKeys ctx (RSA.quadraticWordWidth width)).get
    ⟨index.val, by change index.val < 4; exact index.isLt⟩

private theorem selectorKey_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 4) (different : left ≠ right) :
    selectorKey ctx width left ≠ selectorKey ctx width right := by
  intro same
  have positions :=
    (SelectionLayout.nativeRecovery_selection_nodup ctx
      (RSA.quadraticWordWidth width)).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- Actual candidate allocation discharges all operand distinctions used by the real checks. -/
theorem nativeQuadratic_local_operands_separated
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) :
    CheckLayout.OperandsSeparated (operands modulus) :=
  nativeQuadratic_checkedOperands_separated (arithmeticRead modulus width)
    (arithmeticRefs ctx width) (localRefs ctx width)
    (nativeQuadratic_layout_separated
      (SelectionLayout.underRead modulus (RSA.quadraticWordWidth width)))

/-- Actual local selector and candidate scope positions discharge every selector live range. -/
theorem nativeQuadratic_local_selector_separated
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) :
    CheckLayout.SelectorSeparated (operands modulus) where
  candidateFree := by
    intro key present
    change key ∈ [(localRefs ctx width).available.key, (localRefs ctx width).take.key,
      (localRefs ctx width).accepted.key, (localRefs ctx width).selected.key] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl
    · exact candidate_free (SelectionLayout.available ctx (RSA.quadraticWordWidth width))
    · exact candidate_free (SelectionLayout.take ctx (RSA.quadraticWordWidth width))
    · exact candidate_free (SelectionLayout.accepted ctx (RSA.quadraticWordWidth width))
    · exact candidate_free (SelectionLayout.selected ctx (RSA.quadraticWordWidth width))
  remainderAccepted := Ne.symm
    (old_ne_candidate (SelectionLayout.accepted ctx (RSA.quadraticWordWidth width))
      (arithmeticRefs ctx width).root.key
      (List.get_mem (Layout.internalKeys (selectionContext ctx width) width)
        ⟨2, by change 2 < 4; decide⟩))
  remainderSelected := Ne.symm
    (old_ne_candidate (SelectionLayout.selected ctx (RSA.quadraticWordWidth width))
      (arithmeticRefs ctx width).root.key
      (List.get_mem (Layout.internalKeys (selectionContext ctx width) width)
        ⟨2, by change 2 < 4; decide⟩))
  availableAccepted := selectorKey_ne ctx width 1 3 (by decide)
  takeAccepted := selectorKey_ne ctx width 0 3 (by decide)
  availableSelected := selectorKey_ne ctx width 1 2 (by decide)
  takeSelected := selectorKey_ne ctx width 0 2 (by decide)
  acceptedSelected := selectorKey_ne ctx width 3 2 (by decide)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout
