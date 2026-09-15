/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Layout.Store
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Preservation

/-!
# Actual local scope entry and original source candidate values

The same local selection and candidate allocations establish the real initial
latch values. The subsequent native arithmetic keeps those latches unchanged
and materializes both quadratic candidates from the original stored modulus
and logarithm. The one operand comes from its actual two-instruction loader;
no initialization or nonaliasing condition is imposed on incoming values.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The first eight actual pushes of the complete program enter its local selector and words. -/
def entryStore (width : Nat) (store : Store ctx) : Store (candidateContext ctx width) :=
  Layout.pushStore width (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store)

/-- The same actual initialized candidate program runs on that actual allocated store. -/
noncomputable def initializedStore (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (store : Store ctx) : Store (candidateContext ctx width) :=
  (Initialized.step (arithmeticRead input width) (arithmeticRead modulus width)
    (arithmeticRefs ctx width) (entryStore width store)).1

/-- Actual entry preserves every complete original structural source value. -/
theorem nativeQuadratic_local_entry_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store ctx) :
    (entryStore width store).read (arithmeticRead input width) = store.read input :=
  (Layout.nativeQuadratic_layout_push_read
    (SelectionLayout.underRead input (RSA.quadraticWordWidth width)) width
    (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store)).trans
    (SelectionLayout.nativeRecovery_selection_push_read input (RSA.quadraticWordWidth width) store)

private theorem writes_free {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    ∀ key ∈ writeKeys (Layout.refs ctx width),
      key ∉ (Layout.underRead input width).storageKeys := by
  intro key present
  change key ∈ [(Layout.center ctx width).key, (Layout.root ctx width).key,
    (Layout.first ctx width).key, (Layout.second ctx width).key] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals exact nativeQuadratic_underRead_free input _ (by simp [Layout.internalKeys])

/-- The real initialized candidates equal the original source pair, and the real constant is one.
-/
theorem nativeQuadratic_local_initialized_values (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) (store : Store ctx) :
    let final := initializedStore input modulus store
    ((final.read (.storage (arithmeticRefs ctx width).first.toCStorageRef)).toNat,
        (final.read (.storage (arithmeticRefs ctx width).second.toCStorageRef)).toNat) =
        RSA.quadraticFactorCandidates (store.read modulus).toNat (store.read input).toNat ∧
      (final.read (.storage (arithmeticRefs ctx width).center.toCStorageRef)).toNat = 1 := by
  have actual := Initialized.nativeQuadratic_initialized_values (arithmeticRead input width)
    (arithmeticRead modulus width) (arithmeticRefs ctx width)
    (nativeQuadratic_layout_separated
      (SelectionLayout.underRead modulus (RSA.quadraticWordWidth width))) (entryStore width store)
  exact ⟨actual.1.trans (congrArg₂ RSA.quadraticFactorCandidates
    (congrArg CShape.Value.toNat (nativeQuadratic_local_entry_read modulus width store))
    (congrArg CShape.Value.toNat (nativeQuadratic_local_entry_read input width store))), actual.2⟩

/-- Actual arithmetic leaves the freshly allocated local acceptance flag false. -/
theorem nativeQuadratic_local_initialized_accepted (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) (store : Store ctx) :
    (initializedStore input modulus store).read
        (FirstAccepted.cellRead (localRefs ctx width).accepted) = CShape.Value.bit false := by
  let oldRead := FirstAccepted.cellRead
    (SelectionLayout.accepted ctx (RSA.quadraticWordWidth width))
  have preserved := nativeQuadratic_initialized_read_other (arithmeticRead input width)
    (arithmeticRead modulus width) (arithmeticRefs ctx width) (Layout.underRead oldRead width)
    (writes_free oldRead width) (entryStore width store)
  exact preserved.trans ((Layout.nativeQuadratic_layout_push_read oldRead width
    (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store)).trans
    (SelectionLayout.nativeRecovery_selection_push_accepted (RSA.quadraticWordWidth width) store))

/-- The real local selected word remains its allocated zero until the actual pair selectors run.
-/
theorem nativeQuadratic_local_initialized_selected (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width))) (store : Store ctx) :
    (initializedStore input modulus store).read
        (FirstAccepted.cellRead (localRefs ctx width).selected) =
      CShape.wordOfNat (RSA.quadraticWordWidth width) 0 := by
  let oldRead := FirstAccepted.cellRead
    (SelectionLayout.selected ctx (RSA.quadraticWordWidth width))
  have preserved := nativeQuadratic_initialized_read_other (arithmeticRead input width)
    (arithmeticRead modulus width) (arithmeticRefs ctx width) (Layout.underRead oldRead width)
    (writes_free oldRead width) (entryStore width store)
  exact preserved.trans ((Layout.nativeQuadratic_layout_push_read oldRead width
    (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store)).trans
    (SelectionLayout.nativeRecovery_selection_push_selected (RSA.quadraticWordWidth width) store))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout
