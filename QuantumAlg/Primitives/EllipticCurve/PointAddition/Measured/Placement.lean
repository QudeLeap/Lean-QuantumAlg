/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Physical placement of the actual measured point-addition body

The original measured instructions use injectively mapped storage keys and
physical systems. Both coherent controls, the complete arithmetic work bank
and every finite measurement cell remain resident. Actual Z measurements and
stored-result corrections use the existing interpreter with mapped operands;
their native event and space bounds follow from the same executed body.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement

noncomputable section

open Execution

/-- The complete mapped field, history, measurement-cell and two-control context. -/
@[reducible] def context (width : Nat) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    RuntimeCtx .quantum := (MeasuredPointAddition.context width).relabel keys physical

/-- The same actual measured body with every native address and storage operand mapped. -/
def body {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context p.size keys physical) (context p.size keys physical) allowAllocation :=
  Circuit.embed (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size)
    keys physical) (MeasuredPointAddition.body E Q false)

/-- Each finite path corresponds to the original actual outcomes and selected branches. -/
def pathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (allowAllocation : Bool := true) :
    (MeasuredPointAddition.body E Q false).Path ≃
      (body E Q keys physical allowAllocation).Path :=
  Equiv.refl _

/-- The full physical list is exactly the image of every original live system. -/
lemma context_physical (width : Nat) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (context width keys physical).physicalIdx =
      (MeasuredPointAddition.context width).physicalIdx.map physical :=
  RuntimeCtx.relabel_physicalIdx _ keys physical

/-- Complete original roles retain the same independently prescribed resident space. -/
lemma context_resident (width : Nat) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (context width keys physical).residentSpace = MeasuredPointAddition.space width :=
  (RuntimeCtx.relabel_residentSpace _ keys physical).trans
    (MeasuredPointAddition.context_resident width)

/-- Auxiliary space retains all original owned roles, including both quantum controls. -/
lemma context_auxiliary (width : Nat) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (context width keys physical).auxiliarySpace = MeasuredPointAddition.space width :=
  (RuntimeCtx.relabel_auxiliarySpace _ keys physical).trans
    (MeasuredPointAddition.context_auxiliary width)

attribute [local irreducible] MeasuredPointAddition.body

/-- Every ordered native event survives physical placement of the actual measured instructions. -/
lemma body_eventTrace {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (MeasuredPointAddition.body E Q false).Path) :
    (body E Q keys physical allowAllocation).eventTrace
      (pathEquiv E Q keys physical allowAllocation path) =
      (MeasuredPointAddition.body E Q false).eventTrace path :=
  rfl

/-- Actual emitted resources obey the original independent point-addition budget on every path. -/
lemma body_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical allowAllocation).Path) :
    (body E Q keys physical allowAllocation).resourcePool path ≤
      MeasuredPointAddition.events p.size := by
  change (Circuit.embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical)
    (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size) keys physical)
    (MeasuredPointAddition.body E Q false)).resourcePool path ≤ _
  exact (Circuit.resourcePool_embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical)
    (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size) keys physical)
    (MeasuredPointAddition.body E Q false) path).le.trans
      (MeasuredPointAddition.body_budget (allowAllocation := false) E Q path)

/-- The real placed path keeps the original complete serial native depth bound. -/
lemma body_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical allowAllocation).Path) :
    (body E Q keys physical allowAllocation).depth (fun _ => 1) path ≤
      MeasuredPointAddition.depthBound p.size := by
  change (MeasuredPointAddition.body E Q false).depth (fun _ => 1) path ≤
    MeasuredPointAddition.depthBound p.size
  exact MeasuredPointAddition.body_depth (allowAllocation := false) E Q path

/-- Every original field, work, control and measurement coordinate remains charged at the peak. -/
lemma body_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical allowAllocation).Path) :
    (body E Q keys physical allowAllocation).peakResidentSpace path =
      MeasuredPointAddition.space p.size := by
  change (Circuit.embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical)
    (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size) keys physical)
    (MeasuredPointAddition.body E Q false)).peakResidentSpace path = _
  exact (Circuit.peakResidentSpace_embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical)
    (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size) keys physical)
    (MeasuredPointAddition.body E Q false) path).trans
      (context_resident p.size keys physical)

/-- Auxiliary peaks use the same original complete ownership roles on every actual path. -/
lemma body_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical allowAllocation).Path) :
    (body E Q keys physical allowAllocation).peakAuxiliarySpace path =
      MeasuredPointAddition.space p.size := by
  change (Circuit.embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical)
    (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size) keys physical)
    (MeasuredPointAddition.body E Q false)).peakAuxiliarySpace path = _
  exact (Circuit.peakAuxiliarySpace_embed (model := .quantum AlgorithmGate.model .empty)
    (allowAllocation := allowAllocation)
    (caller := context p.size keys physical)
    (ContextEmbedding.alongRelabeling (MeasuredPointAddition.context p.size) keys physical)
    (MeasuredPointAddition.body E Q false) path).trans
      (context_auxiliary p.size keys physical)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement
