/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement
import all QuantumAlg.Core.Execution.Context.Embedding.Sequence
import all QuantumAlg.Core.Execution.Context.Embedding.Framing

/-!
# Measured point addition beside an actual resident frame

An additional disjoint context stays physically resident throughout the actual
placed point-addition body. All its classical cells and quantum systems enter
the complete state, and its native resident and auxiliary coordinates add to
the point body's independent bound. Full execution retains arbitrary frame
correlations without requiring a separate or unentangled input state.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement
namespace Framing

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution

/-- Every mapped point-body entry and additional frame entry remains in the actual context. -/
@[reducible] def context (width : Nat) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context width keys physical) frame) :
    RuntimeCtx .quantum := (Placement.context width keys physical).disjointUnion frame separate

/-- Native embedding keeps the additional frame resident around every measured instruction. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context p.size keys physical frame separate)
      (context p.size keys physical frame separate) allowAllocation :=
  Circuit.embed (ContextEmbedding.alongUnion (Placement.context p.size keys physical)
    frame separate) (Placement.body E Q keys physical false)

/-- The original point outcomes and selected branches identify every actual enclosing path. -/
def pathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (allowAllocation : Bool := true) :
    (MeasuredPointAddition.body E Q false).Path ≃
      (body E Q keys physical frame separate allowAllocation).Path :=
  Equiv.refl _

attribute [local irreducible] MeasuredPointAddition.body Placement.body

/-- The actual enclosing path emits precisely the original complete point-addition event list. -/
lemma body_eventTrace {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (MeasuredPointAddition.body E Q false).Path) :
    (body E Q keys physical frame separate allowAllocation).eventTrace
      (pathEquiv E Q keys physical frame separate allowAllocation path) =
        (MeasuredPointAddition.body E Q false).eventTrace path := by
  change (Placement.body E Q keys physical false).eventTrace
    (Placement.pathEquiv E Q keys physical false path) = _
  exact Placement.body_eventTrace (allowAllocation := false) E Q keys physical path

/-- The emitted resources meet the original independent bound with the additional frame resident. -/
lemma body_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate allowAllocation).Path) :
    (body E Q keys physical frame separate allowAllocation).resourcePool path ≤
      MeasuredPointAddition.events p.size := by
  change (Circuit.embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical frame separate)
    (ContextEmbedding.alongUnion (Placement.context p.size keys physical) frame separate)
    (Placement.body E Q keys physical false)).resourcePool path ≤ _
  exact (Circuit.resourcePool_embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical frame separate)
    (ContextEmbedding.alongUnion (Placement.context p.size keys physical) frame separate)
    (Placement.body E Q keys physical false) path).le.trans
      (Placement.body_budget (allowAllocation := false) E Q keys physical path)

/-- The actual serial native depth retains its independent point-addition bound. -/
lemma body_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate allowAllocation).Path) :
    (body E Q keys physical frame separate allowAllocation).depth (fun _ => 1) path ≤
      MeasuredPointAddition.depthBound p.size := by
  change (Placement.body E Q keys physical false).depth (fun _ => 1) path ≤ _
  exact Placement.body_depth (allowAllocation := false) E Q keys physical path

/-- Native resident space includes every real system and classical cell in both contexts. -/
lemma body_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate allowAllocation).Path) :
    (body E Q keys physical frame separate allowAllocation).peakResidentSpace path =
      MeasuredPointAddition.space p.size + frame.residentSpace := by
  change (Circuit.embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical frame separate)
    (ContextEmbedding.alongUnion (Placement.context p.size keys physical) frame separate)
    (Placement.body E Q keys physical false)).peakResidentSpace path = _
  exact (Circuit.peakResidentSpace_embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical frame separate)
    (ContextEmbedding.alongUnion (Placement.context p.size keys physical) frame separate)
    (Placement.body E Q keys physical false) path).trans
      ((RuntimeCtx.residentSpace_disjointUnion _ _ separate).trans
        (congrArg (· + frame.residentSpace) (Placement.context_resident p.size keys physical)))

/-- Complete native auxiliary space adds the frame's original fixed-role contribution. -/
lemma body_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate allowAllocation).Path) :
    (body E Q keys physical frame separate allowAllocation).peakAuxiliarySpace path =
      MeasuredPointAddition.space p.size + frame.auxiliarySpace := by
  change (Circuit.embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical frame separate)
    (ContextEmbedding.alongUnion (Placement.context p.size keys physical) frame separate)
    (Placement.body E Q keys physical false)).peakAuxiliarySpace path = _
  exact (Circuit.peakAuxiliarySpace_embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical frame separate)
    (ContextEmbedding.alongUnion (Placement.context p.size keys physical) frame separate)
    (Placement.body E Q keys physical false) path).trans
      ((RuntimeCtx.auxiliarySpace_disjointUnion _ _ separate).trans
        (congrArg (· + frame.auxiliarySpace) (Placement.context_auxiliary p.size keys physical)))

/-- Every frame cell, quantum correlation and actual outcome survives complete execution. -/
lemma body_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (context p.size keys physical frame separate) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) (allowAllocation : Bool := true) :
    ContextUnion.splitServiceState (Placement.context p.size keys physical) frame separate
      ((body E Q keys physical frame separate allowAllocation).execute environment Reference
        original) =
        ((Placement.body E Q keys physical false).execute environment (Register.prod
          frame.register Reference)
          (ContextUnion.splitServiceState (Placement.context p.size keys physical) frame
            separate original)).mapHistory (fun record =>
              (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  Circuit.union_embed_execute (environment := environment)
    (allowAllocation := allowAllocation)
    (Placement.body E Q keys physical false) frame separate Reference original

end

end Framing
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement
