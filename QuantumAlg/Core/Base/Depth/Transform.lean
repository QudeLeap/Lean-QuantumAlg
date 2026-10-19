/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.Depth.Expr
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Relabeling and serialization of depth expressions

These are syntactic laws for every expression constructor. Relabeling preserves
the construction tree; optional serialization replaces every tensor by a
sequence. A physical control implementation must establish separately that its
actual event schedule is this transform. The scalar laws impose no event model,
wire width, duration, or execution-state premise.
-/

namespace QuantumAlg.DepthExpr

open scoped BigOperators

variable {U V W M N : Type}

/-- Relabel every atom and optionally serialize all tensor branches. -/
public def mapSchedule (serialize : Bool) (relabel : U → V) : DepthExpr U → DepthExpr V
  | .id => .id
  | .atom event => .atom (relabel event)
  | .seq left right => .seq (mapSchedule serialize relabel left)
      (mapSchedule serialize relabel right)
  | .tensor left right =>
      if serialize then .seq (mapSchedule serialize relabel left)
        (mapSchedule serialize relabel right)
      else .tensor (mapSchedule serialize relabel left) (mapSchedule serialize relabel right)
  | .inverse body => .inverse (mapSchedule serialize relabel body)
  | .controlled label body => .controlled label (mapSchedule serialize relabel body)
  | .iterate count body => .iterate count (mapSchedule serialize relabel body)
  | .indexedProduct label count start step =>
      .indexedProduct label count (mapSchedule serialize relabel start)
        (fun index => mapSchedule serialize relabel (step index))

@[simp] lemma mapSchedule_false_id (expression : DepthExpr U) :
    mapSchedule false (fun unit => unit) expression = expression := by
  induction expression <;> simp [mapSchedule, *]

/-- Successive relabelings compose, and any serialization remains in force. -/
lemma mapSchedule_comp (first second : Bool) (inner : U → V) (outer : V → W)
    (expression : DepthExpr U) :
    mapSchedule second outer (mapSchedule first inner expression) =
      mapSchedule (first || second) (outer ∘ inner) expression := by
  induction expression <;> cases first <;> cases second <;>
    simp [mapSchedule, Function.comp_def, *]

/-- The same linear total work is evaluated under the relabeled atom weights. -/
lemma costEval_mapSchedule [AddCommMonoid M] (assign : V → M)
    (serialize : Bool) (relabel : U → V) (expression : DepthExpr U) :
    costEval assign (mapSchedule serialize relabel expression) =
      costEval (assign ∘ relabel) expression := by
  induction expression <;> cases serialize <;>
    simp [mapSchedule, Function.comp_def, *]

/-- Relabeling alone preserves max-plus depth; serialization gives total work. -/
lemma depthEval_mapSchedule (assign : V → Nat) (serialize : Bool)
    (relabel : U → V) (expression : DepthExpr U) :
    depthEval assign (mapSchedule serialize relabel expression) =
      if serialize then costEval (assign ∘ relabel) expression
      else depthEval (assign ∘ relabel) expression := by
  induction expression <;> cases serialize <;>
    simp [mapSchedule, Function.comp_def, *]

/-- Injective relabeling retains the exact focus coordinate and its query count. -/
lemma queryDepthEval_mapSchedule [DecidableEq U] [DecidableEq V]
    (focus : U) (serialize : Bool) (relabel : U → V)
    (injective : Function.Injective relabel) (expression : DepthExpr U) :
    queryDepthEval (relabel focus) (mapSchedule serialize relabel expression) =
      if serialize then costEval (indicator focus) expression
      else queryDepthEval focus expression := by
  have weights : indicator (relabel focus) ∘ relabel = indicator focus := by
    funext event
    simp [indicator, injective.eq_iff]
  simp only [queryDepthEval, depthEval_mapSchedule, weights]

/-- Any additive interpretation commutes with collecting the expression's atoms.
This includes mapping its literal multiset ledger, without enumerating atoms. -/
lemma costEval_mapAddMonoidHom [AddCommMonoid M] [AddCommMonoid N]
    (morphism : M →+ N) (assign : U → M) (expression : DepthExpr U) :
    costEval (morphism ∘ assign) expression = morphism (costEval assign expression) := by
  induction expression <;>
    simp_all [Function.comp_def, costEval]

end QuantumAlg.DepthExpr
