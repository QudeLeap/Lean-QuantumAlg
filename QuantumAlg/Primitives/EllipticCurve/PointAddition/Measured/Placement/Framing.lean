/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement
import all QuantumAlg.Core.Execution.Local.Framing.State

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

open Execution

/-- Every mapped point-body entry and additional frame entry remains in the actual context. -/
@[reducible] def context (width : Nat) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context width keys physical) frame) :
    RuntimeCtx .quantum := (Placement.context width keys physical).disjointUnion frame separate

/-- The actual compiler keeps the additional frame resident around every measured instruction. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context p.size keys physical frame separate)
      (context p.size keys physical frame separate) :=
  ContextUnion.frameLocal (Placement.body E Q keys physical)
    (Placement.body_isLocal E Q keys physical) frame separate

/-- The original point outcomes and selected branches identify every actual enclosing path. -/
def pathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame) :
    (MeasuredPointAddition.body E Q).Path ≃ (body E Q keys physical frame separate).Path :=
  (Placement.pathEquiv E Q keys physical).trans
    (ContextUnion.frameLocalPathEquiv (Placement.body E Q keys physical)
      (Placement.body_isLocal E Q keys physical) frame separate)

/-- All enclosing instructions remain in the same local fragment of the existing interpreter. -/
theorem body_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame) :
    (body E Q keys physical frame separate).IsLocal :=
  ContextUnion.frameLocal_isLocal _ (Placement.body_isLocal E Q keys physical) frame separate

/-- The actual enclosing path emits precisely the original complete point-addition event list. -/
theorem body_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (MeasuredPointAddition.body E Q).Path) :
    (body E Q keys physical frame separate).eventTrace
      (pathEquiv E Q keys physical frame separate path) =
        (MeasuredPointAddition.body E Q).eventTrace path :=
  (ContextUnion.frameLocal_eventTrace _ (Placement.body_isLocal E Q keys physical) frame separate
    (Placement.pathEquiv E Q keys physical path)).trans
      (Placement.body_eventTrace E Q keys physical path)

/-- The emitted resources meet the original independent bound with the additional frame resident. -/
theorem body_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate).Path) :
    (body E Q keys physical frame separate).resourcePool path ≤
      MeasuredPointAddition.events p.size := by
  obtain ⟨original, rfl⟩ := (pathEquiv E Q keys physical frame separate).surjective path
  exact (congrArg ResourcePool.ofList
    (body_eventTrace E Q keys physical frame separate original)).le.trans
      (MeasuredPointAddition.body_budget E Q original)

/-- The actual serial native depth retains its independent point-addition bound. -/
theorem body_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate).Path) :
    (body E Q keys physical frame separate).depth (fun _ => 1) path ≤
      MeasuredPointAddition.depthBound p.size := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv
    (Placement.body E Q keys physical) (Placement.body_isLocal E Q keys physical)
    frame separate).surjective path
  exact (ContextUnion.frameLocal_depth _ (Placement.body_isLocal E Q keys physical)
    frame separate (fun _ => 1) original).le.trans
      (Placement.body_depth E Q keys physical original)

/-- Native resident space includes every real system and classical cell in both contexts. -/
theorem body_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate).Path) :
    (body E Q keys physical frame separate).peakResidentSpace path =
      MeasuredPointAddition.space p.size + frame.residentSpace :=
  (ContextUnion.frameLocal_peakResidentSpace _ (Placement.body_isLocal E Q keys physical)
    frame separate path).trans
      (congrArg (· + frame.residentSpace) (Placement.context_resident p.size keys physical))

/-- Complete native auxiliary space adds the frame's original fixed-role contribution. -/
theorem body_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    (path : (body E Q keys physical frame separate).Path) :
    (body E Q keys physical frame separate).peakAuxiliarySpace path =
      MeasuredPointAddition.space p.size + frame.auxiliarySpace :=
  (ContextUnion.frameLocal_peakAuxiliarySpace _ (Placement.body_isLocal E Q keys physical)
    frame separate path).trans
      (congrArg (· + frame.auxiliarySpace) (Placement.context_auxiliary p.size keys physical))

/-- Every frame cell, quantum correlation and actual outcome survives complete execution. -/
theorem body_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint (Placement.context p.size keys physical) frame)
    {Reference : Register} {H : Type} [Fintype H]
    (original : State (context p.size keys physical frame separate) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ContextUnion.splitServiceState (Placement.context p.size keys physical) frame separate
      ((body E Q keys physical frame separate).execute Reference original) =
        ((Placement.body E Q keys physical).execute (Register.prod frame.register Reference)
          (ContextUnion.splitServiceState (Placement.context p.size keys physical) frame
            separate original)).mapHistory (fun record =>
              (record.1, (record.2.1.1, (record.2.1.2,
                ContextUnion.frameLocalPathEquiv _
                  (Placement.body_isLocal E Q keys physical) frame separate record.2.2)))) :=
  ContextUnion.frameLocal_execute _ (Placement.body_isLocal E Q keys physical)
    frame separate Reference original

end

end Framing
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement
