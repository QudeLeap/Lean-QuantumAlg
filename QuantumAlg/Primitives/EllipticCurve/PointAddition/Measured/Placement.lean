/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Core.Execution.Context.Relabeling.Local.Resources

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
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (context p.size keys physical) (context p.size keys physical) :=
  ContextRelabeling.localCircuit (MeasuredPointAddition.body E Q)
    (MeasuredPointAddition.body_isLocal E Q) keys physical

/-- Each finite path corresponds to the original actual outcomes and selected branches. -/
def pathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (MeasuredPointAddition.body E Q).Path ≃ (body E Q keys physical).Path :=
  ContextRelabeling.localPathEquiv (MeasuredPointAddition.body E Q)
    (MeasuredPointAddition.body_isLocal E Q) keys physical

/-- Placement keeps the body in the original allocation-free circuit fragment. -/
theorem body_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat) :
    (body E Q keys physical).IsLocal :=
  ContextRelabeling.localCircuit_isLocal _ (MeasuredPointAddition.body_isLocal E Q) keys physical

/-- The full physical list is exactly the image of every original live system. -/
theorem context_physical (width : Nat) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (context width keys physical).physicalIdx =
      (MeasuredPointAddition.context width).physicalIdx.map physical :=
  RuntimeCtx.relabel_physicalIdx _ keys physical

/-- Complete original roles retain the same independently prescribed resident space. -/
theorem context_resident (width : Nat) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (context width keys physical).residentSpace = MeasuredPointAddition.space width :=
  (RuntimeCtx.relabel_residentSpace _ keys physical).trans
    (MeasuredPointAddition.context_resident width)

/-- Auxiliary space retains all original owned roles, including both quantum controls. -/
theorem context_auxiliary (width : Nat) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) :
    (context width keys physical).auxiliarySpace = MeasuredPointAddition.space width :=
  (RuntimeCtx.relabel_auxiliarySpace _ keys physical).trans
    (MeasuredPointAddition.context_auxiliary width)

/-- Every ordered native event survives physical placement of the actual measured instructions. -/
theorem body_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (MeasuredPointAddition.body E Q).Path) :
    (body E Q keys physical).eventTrace (pathEquiv E Q keys physical path) =
      (MeasuredPointAddition.body E Q).eventTrace path :=
  ContextRelabeling.localCircuit_eventTrace _ (MeasuredPointAddition.body_isLocal E Q)
    keys physical path

/-- Actual emitted resources obey the original independent point-addition budget on every path. -/
theorem body_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical).Path) :
    (body E Q keys physical).resourcePool path ≤ MeasuredPointAddition.events p.size := by
  obtain ⟨original, rfl⟩ := (pathEquiv E Q keys physical).surjective path
  exact (ContextRelabeling.localCircuit_resourcePool _ (MeasuredPointAddition.body_isLocal E Q)
    keys physical original).le.trans (MeasuredPointAddition.body_budget E Q original)

/-- The real placed path keeps the original complete serial native depth bound. -/
theorem body_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical).Path) :
    (body E Q keys physical).depth (fun _ => 1) path ≤
      MeasuredPointAddition.depthBound p.size := by
  obtain ⟨original, rfl⟩ := (pathEquiv E Q keys physical).surjective path
  exact (ContextRelabeling.localCircuit_depth _ (MeasuredPointAddition.body_isLocal E Q)
    keys physical (fun _ => 1) original).le.trans (MeasuredPointAddition.body_depth E Q original)

/-- Every original field, work, control and measurement coordinate remains charged at the peak. -/
theorem body_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical).Path) :
    (body E Q keys physical).peakResidentSpace path = MeasuredPointAddition.space p.size :=
  (ContextRelabeling.localCircuit_peakResidentSpace _ (MeasuredPointAddition.body_isLocal E Q)
    keys physical path).trans (MeasuredPointAddition.context_resident p.size)

/-- Auxiliary peaks use the same original complete ownership roles on every actual path. -/
theorem body_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (path : (body E Q keys physical).Path) :
    (body E Q keys physical).peakAuxiliarySpace path = MeasuredPointAddition.space p.size :=
  (ContextRelabeling.localCircuit_peakAuxiliarySpace _ (MeasuredPointAddition.body_isLocal E Q)
    keys physical path).trans (MeasuredPointAddition.context_auxiliary p.size)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Placement
