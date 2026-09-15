/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Owned.CircuitRestoration

/-!
# Actual repeated right shifts of the decoded terminal word

The source sample split divides the full terminal index by `2 ^ ell` using
exactly ell native one-bit shifts. The existing iterate constructor performs
those real operations and records every path. Any original target value is
allowed, and other structural reads remain unchanged. The same construction
also includes zero shifts and zero-width words.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalShift

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- One actual in-place right shift of the decoded terminal word. -/
def shiftOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (.storage output.toCStorageRef) output

/-- The literal fixed number of native shifts required by the original sample split. -/
def code (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .iterate count (.classical (shiftOp output))

/-- The store update iterates exactly the same native word instruction. -/
def storeStep (count : Nat) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  (fun current => current.applyOp (shiftOp output))^[count] store

/-- The real shift stores the unsigned quotient by two without further truncation. -/
theorem nativeRecovery_terminal_shift_read (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((store.applyOp (shiftOp output)).read (.storage output.toCStorageRef)).toNat =
      (store.read (.storage output.toCStorageRef)).toNat / 2 := by
  have actual := congrArg CShape.Value.toNat (Store.read_applyOp_output store (shiftOp output))
  change ((store.applyOp (shiftOp output)).read (.storage output.toCStorageRef)).toNat =
    ((store.read (.storage output.toCStorageRef)).toNat / 2) % 2 ^ width at actual
  exact actual.trans (Nat.mod_eq_of_lt
    ((Nat.div_le_self _ _).trans_lt (store.read (.storage output.toCStorageRef)).toNat_lt))

/-- Every actual finite shift sequence computes the exact source quotient by a power of two. -/
theorem nativeRecovery_terminal_shifts_read (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((storeStep count output store).read (.storage output.toCStorageRef)).toNat =
      (store.read (.storage output.toCStorageRef)).toNat / 2 ^ count := by
  induction count generalizing store with
  | zero => simp only [storeStep, Function.iterate_zero_apply, Nat.pow_zero, Nat.div_one]
  | succ count ih =>
      have later := ih (store.applyOp (shiftOp output))
      change ((storeStep count output (store.applyOp (shiftOp output))).read
        (.storage output.toCStorageRef)).toNat = _
      refine later.trans ?_
      rw [nativeRecovery_terminal_shift_read, Nat.div_div_eq_div_mul, Nat.pow_succ,
        Nat.mul_comm 2 (2 ^ count)]

/-- The actual repeated writes preserve every original read outside the single destination. -/
theorem nativeRecovery_terminal_shifts_read_other (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (different : output.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep count output store).read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change (storeStep count output (store.applyOp (shiftOp output))).read other = _
      exact (ih _).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (shiftOp output) other different)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual shift iteration preserves every store-keyed quantum-reference block and true path. -/
theorem nativeRecovery_terminal_shifts_execute (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code count output).execute Reference state = state.mapClassical (fun entry =>
      (storeStep count output entry.1, (entry.2, fun _ : Fin count => ()))) := by
  refine (Circuit.execute_iterate_mapClassical (.classical (shiftOp output))
    (fun current => (current.applyOp (shiftOp output), ()))
    (fun reference {history} _ current => by
      refine (Circuit.execute_classical_mapClassical (shiftOp output) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).symm)
    count Reference state).trans ?_
  dsimp only [storeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (Fin count → Unit)))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (Fin count → Unit)))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

private theorem flatten_repeated_singleton {α : Type} (count : Nat) (value : α) :
    (List.ofFn (fun _ : Fin count => [value])).flatten = List.replicate count value := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [List.ofFn_succ, List.flatten_cons, List.singleton_append,
      List.replicate_succ] using congrArg (List.cons value) ih

/-- The exact chronological trace contains exactly the real requested number of shifts. -/
theorem nativeRecovery_terminal_shifts_trace (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (path : (code count output).Path) :
    (code count output).eventTrace path =
      List.replicate count (.classicalOperation (.wordUnary .shiftRight width)) :=
  flatten_repeated_singleton count _

/-- Independent literal native allowance for the original fixed shift count. -/
def nativeEnvelope (kind : ProblemKind) (width count : Nat) : ResourcePool kind :=
  ResourcePool.ofList
    (List.replicate count (.classicalOperation (.wordUnary .shiftRight width)))

/-- Every real path has exactly the independent native multiplicity. -/
theorem nativeRecovery_terminal_shifts_pool (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (path : (code count output).Path) :
    (code count output).resourcePool path = nativeEnvelope kind width count :=
  congrArg ResourcePool.ofList (nativeRecovery_terminal_shifts_trace count output path)

/-- Each real shift is charged in the actual serial dependency chain. -/
theorem nativeRecovery_terminal_shifts_depth (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (code count output).Path) :
    (code count output).depth duration path =
      count * duration (.classicalOperation (.wordUnary .shiftRight width)) := by
  change 0 + (∑ _ : Fin count, duration (.classicalOperation (.wordUnary .shiftRight width))) = _
  simp

/-- The complete actual iteration restores the borrowed classical-quantum-reference interface. -/
theorem nativeRecovery_terminal_shifts_borrowedRestored (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code count output).BorrowedRestored Reference state
      ((code count output).execute Reference state) :=
  Circuit.borrowedRestored_iterate (.classical (shiftOp output)) Reference
    (fun {_} _ current => Circuit.borrowedRestored_classical (shiftOp output) current) count state

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalShift
