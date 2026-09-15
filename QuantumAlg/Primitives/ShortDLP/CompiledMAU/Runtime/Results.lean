/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Distinct chronological result cells for the reusable short-DLP bank

Each round retains one actual packed-result cell before running. The final
structural vector reads these distinct cells in round order. All older cells,
including the sampled parameter and the shared finite measurement cells,
remain accessible underneath the subsequent retained results. This layout
adds classical capacity only; the ordered physical quantum bank is unchanged.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeResults

noncomputable section

variable (m ell width : Nat)

/-- The next round's single actual packed-result cell. -/
def next (ctx : RuntimeCtx .quantum) : RuntimeCtx .quantum :=
  ctx.addRetained ctx.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
    ctx.canonicalFreshKey_fresh

/-- The final context after retaining the requested chronological result cells. -/
def context (m ell width : Nat) : (ctx : RuntimeCtx .quantum) → Nat → RuntimeCtx .quantum
  | ctx, 0 => ctx
  | ctx, count + 1 => context m ell width (next m ell width ctx) count

/-- The new round writes its packed measurement directly to this cell. -/
def head (ctx : RuntimeCtx .quantum) :
    CWriteRef (next m ell width ctx) (.bits (RuntimeRound.resultBits m ell width)) :=
  .retainedHead ctx ctx.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
    ctx.canonicalFreshKey_fresh

/-- Keep an existing structural input below every subsequent result cell. -/
def liftInput (m ell width : Nat) {shape : CShape} : {ctx : RuntimeCtx .quantum} →
    CInputRef ctx shape → (count : Nat) → CInputRef (context m ell width ctx count) shape
  | _, input, 0 => input
  | ctx, input, count + 1 => liftInput m ell width
      (input.underRetained ctx.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
        ctx.canonicalFreshKey_fresh) count

/-- Keep an existing writable cell below every subsequent result cell. -/
def liftWrite (m ell width : Nat) {shape : CShape} : {ctx : RuntimeCtx .quantum} →
    CWriteRef ctx shape → (count : Nat) → CWriteRef (context m ell width ctx count) shape
  | _, ref, 0 => ref
  | ctx, ref, count + 1 => liftWrite m ell width
      (ref.underRetained ctx.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
        ctx.canonicalFreshKey_fresh) count

/-- Final references enumerate the result cells in the order their rounds run. -/
def reference (m ell width : Nat) : (ctx : RuntimeCtx .quantum) → (count : Nat) →
    Fin count → CWriteRef (context m ell width ctx count)
      (.bits (RuntimeRound.resultBits m ell width))
  | _, 0, index => Fin.elim0 index
  | ctx, count + 1, index => Fin.cases
      (liftWrite m ell width (head m ell width ctx) count)
      (reference m ell width (next m ell width ctx) count) index

/-- Reading the vector observes real stored results and performs no hidden conversion. -/
def input (ctx : RuntimeCtx .quantum) (count : Nat) :
    CInputRef (context m ell width ctx count)
      (.fixedVector count (.bits (RuntimeRound.resultBits m ell width))) :=
  .fixedVector fun index => .storage (reference m ell width ctx count index).toCStorageRef

/-- The new cell does not change any quantum wire's identity, dimension or order. -/
theorem shortDLP_runtimeResult_next_wires (ctx : RuntimeCtx .quantum) :
    (next m ell width ctx).quantumWires = ctx.quantumWires :=
  RuntimeCtx.quantumWires_addRetained ctx ctx.canonicalFreshKey
    (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh

/-- Arbitrarily many recorded outcomes keep precisely the same physical bank. -/
theorem shortDLP_runtimeResults_wires (ctx : RuntimeCtx .quantum) (count : Nat) :
    (context m ell width ctx count).quantumWires = ctx.quantumWires := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact (induction (next m ell width ctx)).trans
        (shortDLP_runtimeResult_next_wires m ell width ctx)

/-- Every actually retained result contributes its full declared classical capacity. -/
theorem shortDLP_runtimeResults_resident (ctx : RuntimeCtx .quantum) (count : Nat) :
    (context m ell width ctx count).residentSpace =
      count • SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width)) +
        ctx.residentSpace := by
  induction count generalizing ctx with
  | zero => simp only [context, zero_nsmul, zero_add]
  | succ count induction =>
      rw [context, induction, next, RuntimeCtx.residentSpace_addRetained, succ_nsmul]
      ac_rfl

/-- Retained outcomes also remain present in the actual auxiliary-space accounting. -/
theorem shortDLP_runtimeResults_auxiliary (ctx : RuntimeCtx .quantum) (count : Nat) :
    (context m ell width ctx count).auxiliarySpace =
      count • SpacePool.ofShape (.bits (RuntimeRound.resultBits m ell width)) +
        ctx.auxiliarySpace := by
  induction count generalizing ctx with
  | zero => simp only [context, zero_nsmul, zero_add]
  | succ count induction =>
      rw [context, induction, next, RuntimeCtx.auxiliarySpace_addRetained, succ_nsmul]
      ac_rfl

/-- Input lifting agrees with the same existing cell's writable-reference lift. -/
theorem shortDLP_runtimeResults_lift_storage {ctx : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef ctx shape) (count : Nat) :
    liftInput m ell width (.storage ref.toCStorageRef) count =
      .storage (liftWrite m ell width ref count).toCStorageRef := by
  induction count generalizing ctx with
  | zero => rfl
  | succ count induction =>
      exact induction (ref.underRetained ctx.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) ctx.canonicalFreshKey_fresh)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeResults
