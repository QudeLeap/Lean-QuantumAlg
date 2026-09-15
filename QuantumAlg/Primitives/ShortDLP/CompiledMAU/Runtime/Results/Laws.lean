/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Separation and chronological reads of the actual result cells

Every result retained by the repeated circuit has a fresh storage identity.
The cells are pairwise distinct and disjoint from all pre-existing inputs,
including the sampled parameter and the shared finite measurement cells.
Lifting references preserves their exact keys and structural support.

The final vector decomposes into the actual first result followed by the
recursive tail. These are layout facts for the real circuit, rather than
additional assumptions about its incoming state or a duplicate output store.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeResults

noncomputable section

open Execution

variable (m ell width : Nat)

/-- Moving an old writable reference under later results preserves its storage identity. -/
theorem shortDLP_runtimeResults_liftWrite_key {ctx : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef ctx shape) (count : Nat) :
    (liftWrite m ell width ref count).key = ref.key := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact induction (ref.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)

/-- Existing structural inputs traverse exactly the same keys after all result allocations. -/
theorem shortDLP_runtimeResults_liftInput_keys {ctx : RuntimeCtx .quantum} {shape : CShape}
    (input : CInputRef ctx shape) (count : Nat) :
    (liftInput m ell width input count).storageKeys = input.storageKeys := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact (induction (input.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)).trans
        (CInputRef.storageKeys_underRetained input ctx.canonicalFreshKey
          (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)

/-- Each newly recorded result is separate from every entry present before repetition. -/
theorem shortDLP_runtimeResults_reference_fresh (ctx : RuntimeCtx .quantum) (count : Nat)
    (index : Fin count) :
    (reference m ell width ctx count index).key ∉ ctx.keys := by
  induction count generalizing ctx with
  | zero => exact Fin.elim0 index
  | succ count induction =>
      refine Fin.cases ?_ (fun index => ?_) index
      · exact (shortDLP_runtimeResults_liftWrite_key m ell width
          (head m ell width ctx) count).symm ▸ ctx.canonicalFreshKey_fresh
      · intro present
        apply induction (next m ell width ctx) index
        exact List.mem_cons_of_mem _ present

/-- Chronological result references denote pairwise distinct live storage cells. -/
theorem shortDLP_runtimeResults_reference_injective (ctx : RuntimeCtx .quantum) (count : Nat) :
    Function.Injective (fun index => (reference m ell width ctx count index).key) := by
  induction count generalizing ctx with
  | zero => intro index; exact Fin.elim0 index
  | succ count induction =>
      intro left right same
      revert same
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          have headKey := shortDLP_runtimeResults_liftWrite_key m ell width
            (head m ell width ctx) count
          have distinct := shortDLP_runtimeResults_reference_fresh m ell width
            (next m ell width ctx) count right
          apply False.elim
          apply distinct
          have keyEq : (reference m ell width (next m ell width ctx) count right).key =
              ctx.canonicalFreshKey := same.symm.trans headKey
          exact keyEq.symm ▸ List.mem_cons_self
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          have headKey := shortDLP_runtimeResults_liftWrite_key m ell width
            (head m ell width ctx) count
          have distinct := shortDLP_runtimeResults_reference_fresh m ell width
            (next m ell width ctx) count left
          apply False.elim
          apply distinct
          have keyEq : (reference m ell width (next m ell width ctx) count left).key =
              ctx.canonicalFreshKey := same.trans headKey
          exact keyEq.symm ▸ List.mem_cons_self
        · intro same
          exact congrArg Fin.succ (induction (next m ell width ctx) same)

/-- An old structural operand cannot alias any of the newly retained results. -/
theorem shortDLP_runtimeResults_reference_separate {ctx : RuntimeCtx .quantum}
    {shape : CShape} (input : CInputRef ctx shape) (count : Nat) (index : Fin count) :
    (reference m ell width ctx count index).key ∉
      (liftInput m ell width input count).storageKeys := by
  rw [shortDLP_runtimeResults_liftInput_keys]
  exact fun present => shortDLP_runtimeResults_reference_fresh m ell width ctx count index
    (CInputRef.storageKeys_subset_context input present)

/-- Every pre-existing writable cell is disjoint from the complete recorded result vector. -/
theorem shortDLP_runtimeResults_oldWrite_separate {ctx : RuntimeCtx .quantum}
    {shape : CShape} (ref : CWriteRef ctx shape) (count : Nat) :
    (liftWrite m ell width ref count).key ∉ (input m ell width ctx count).storageKeys := by
  intro present
  obtain ⟨keys, listed, member⟩ := List.mem_flatten.mp present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp listed
  have same := List.mem_singleton.mp member
  have original := shortDLP_runtimeResults_liftWrite_key m ell width ref count
  have live : ref.key ∈ ctx.keys :=
    List.mem_map.mpr ⟨.storage ref.key ref.toCStorageRef.role shape,
      ref.toCStorageRef.present, rfl⟩
  exact shortDLP_runtimeResults_reference_fresh m ell width ctx count index
    ((same.symm.trans original).symm ▸ live)

/-- The actual vector read consists of the first retained result and the recursive tail. -/
theorem shortDLP_runtimeResults_read_succ (ctx : RuntimeCtx .quantum) (count : Nat)
    (store : Store (context m ell width ctx (count + 1))) :
    store.read (input m ell width ctx (count + 1)) =
      .fixedVector (Fin.cons
        (store.read (.storage (liftWrite m ell width (head m ell width ctx) count).toCStorageRef))
        (fun index => store.read (.storage
          (reference m ell width (next m ell width ctx) count index).toCStorageRef))) := by
  apply congrArg CShape.Value.fixedVector
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeResults
