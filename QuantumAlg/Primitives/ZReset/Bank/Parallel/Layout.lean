/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ClassicalOp
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Parent-owned scalar outcome storage for a parallel bank reset

Every reset wire has its own finite two-valued workspace entry. The parent
opens and later closes these scopes; the fixed measurement/correction body
allocates nothing. Distinct storage identities allow all outcomes to remain
available until the one parallel correction layer. Original live entries
are never used as scratch, even when their values are correlated with a
reference or retained for a later classical consumer.
-/

namespace QuantumAlg.ZReset.BankParallel.Workspace

variable {kind : ProblemKind}

/-- The parent reserves one distinct lexical result cell per reset wire. -/
@[implicit_reducible] public def context (ctx : RuntimeCtx kind) : Nat → RuntimeCtx kind
  | 0 => ctx
  | count + 1 =>
      (context ctx count).addWorkspace (context ctx count).canonicalFreshKey
        (.finite 2) (context ctx count).canonicalFreshKey_fresh

/-- Index zero is the newest scratch cell; earlier cells remain distinct. -/
@[implicit_reducible] public def reference (ctx : RuntimeCtx kind) :
    (count : Nat) → Fin count → CWriteRef (context ctx count) (.finite 2)
  | 0, index => Fin.elim0 index
  | count + 1, index =>
      Fin.cases
        (CWriteRef.workspaceHead (context ctx count) (context ctx count).canonicalFreshKey
          (.finite 2) (context ctx count).canonicalFreshKey_fresh)
        (fun previous => (reference ctx count previous).underWorkspace
          (context ctx count).canonicalFreshKey (.finite 2)
          (context ctx count).canonicalFreshKey_fresh) index

/-- A structural vector reads precisely the real separately allocated outcomes. -/
public def input (ctx : RuntimeCtx kind) (count : Nat) :
    CInputRef (context ctx count) (.fixedVector count (.finite 2)) :=
  .fixedVector fun index => .storage (reference ctx count index).toCStorageRef

/-- Existing writable entries cross the parent scopes without copying their values. -/
public def liftWrite {ctx : RuntimeCtx kind} {shape : CShape} (ref : CWriteRef ctx shape) :
    (count : Nat) → CWriteRef (context ctx count) shape
  | 0 => ref
  | count + 1 =>
      (liftWrite ref count).underWorkspace (context ctx count).canonicalFreshKey
        (.finite 2) (context ctx count).canonicalFreshKey_fresh

private lemma reference_key_mem {ctx : RuntimeCtx kind} {shape : CShape}
    (ref : CStorageRef ctx shape) : ref.key ∈ ctx.keys :=
  List.mem_map.mpr ⟨.storage ref.key ref.role shape, ref.present, rfl⟩

/-- Simultaneously retained outcomes never alias one another. -/
public lemma reference_key_injective (ctx : RuntimeCtx kind) (count : Nat) :
    Function.Injective (fun index => (reference ctx count index).key) := by
  induction count with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right same
      revert same
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          change (context ctx count).canonicalFreshKey =
            (reference ctx count right).key at same
          have present := reference_key_mem (reference ctx count right).toCStorageRef
          exact False.elim ((context ctx count).canonicalFreshKey_fresh
            (same.symm ▸ present))
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          change (reference ctx count left).key =
            (context ctx count).canonicalFreshKey at same
          have present := reference_key_mem (reference ctx count left).toCStorageRef
          exact False.elim ((context ctx count).canonicalFreshKey_fresh
            (same ▸ present))
        · intro same
          exact congrArg Fin.succ (ih same)

/-- Parent scratch allocation changes no ordered physical wire record. -/
public lemma context_quantumWires (ctx : RuntimeCtx kind) (count : Nat) :
    (context ctx count).quantumWires = ctx.quantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [context, RuntimeCtx.quantumWires_addWorkspace] using ih

/-- Scalar scratch cells add no physical quantum systems. -/
public lemma context_systemCount (ctx : RuntimeCtx kind) (count : Nat) :
    (context ctx count).systemCount = ctx.systemCount :=
  congrArg List.length (context_quantumWires ctx count)

/-- Each scalar outcome contributes exactly one finite-two capacity to resident space. -/
public lemma context_residentSpace (ctx : RuntimeCtx kind) (count : Nat) :
    (context ctx count).residentSpace =
      count • SpacePool.ofShape (.finite 2) + ctx.residentSpace := by
  induction count with
  | zero => simp only [context, zero_nsmul, zero_add]
  | succ count ih =>
      rw [context, RuntimeCtx.residentSpace_addWorkspace, ih, succ_nsmul]
      ac_rfl

/-- The same parent scratch cells contribute to the auxiliary peak. -/
public lemma context_auxiliarySpace (ctx : RuntimeCtx kind) (count : Nat) :
    (context ctx count).auxiliarySpace =
      count • SpacePool.ofShape (.finite 2) + ctx.auxiliarySpace := by
  induction count with
  | zero => simp only [context, zero_nsmul, zero_add]
  | succ count ih =>
      rw [context, RuntimeCtx.auxiliarySpace_addWorkspace, ih, succ_nsmul]
      ac_rfl

/-- Quantum positions are transported through actual classical scopes only. -/
public def wireEquiv (ctx : RuntimeCtx kind) :
    (count : Nat) → Fin ctx.systemCount ≃ Fin (context ctx count).systemCount
  | 0 => Equiv.refl _
  | count + 1 => wireEquiv ctx count

/-- Every transported position has the same physical identity and dimension. -/
public lemma wireEquiv_preserved (ctx : RuntimeCtx kind) (count : Nat)
    (wire : Fin ctx.systemCount) :
    (context ctx count).quantumLayout.wire (wireEquiv ctx count wire) =
      ctx.quantumLayout.wire wire := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

end QuantumAlg.ZReset.BankParallel.Workspace
