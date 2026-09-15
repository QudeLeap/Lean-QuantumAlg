/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset

/-!
# Finite native reset branch allowances

Each physical wire executes one Z event, its actual stored-outcome negative
shift, and its specified seed shift. The native pool allowance includes each
possible correction label once at that position. This coordinate allowance
is distinct from the actual event count, which remains exactly three per
wire. Arbitrary durations retain the selected correction and prescribed seed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution

private def resetWireBudget {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (label : ctx.quantumLayout.Basis) : ResourcePool .quantum :=
  ResourcePool.ofList [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension,
    .gate (QuditShift.gateLabel (label wire))] +
      ∑ amount : Fin (ctx.quantumLayout.wire wire).dimension,
        ResourcePool.singleton (.gate (QuditShift.gateLabel amount))

private def resetWireDepth {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (label : ctx.quantumLayout.Basis) (duration : Resource.Event .quantum → Nat) : Nat :=
  duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
    Finset.univ.sup (fun amount : Fin (ctx.quantumLayout.wire wire).dimension =>
      duration (.gate (QuditShift.gateLabel amount))) +
        duration (.gate (QuditShift.gateLabel (label wire)))

private theorem resetWire_pool_le {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis)
    (path : (QuditShift.resetWireToBasis wire output (label wire)).Path) :
    (QuditShift.resetWireToBasis wire output (label wire)).resourcePool path ≤
      resetWireBudget wire label := by
  have correction :
      ResourcePool.singleton (.gate (QuditShift.gateLabel (-path.1.2.1.toFin))) ≤
        ∑ amount : Fin (ctx.quantumLayout.wire wire).dimension,
          ResourcePool.singleton (.gate (QuditShift.gateLabel amount)) :=
    Finset.single_le_sum
      (f := fun amount : Fin (ctx.quantumLayout.wire wire).dimension =>
        ResourcePool.singleton (.gate (QuditShift.gateLabel amount)))
      (fun _ _ => zero_le) (Finset.mem_univ (-path.1.2.1.toFin))
  rw [QuditShift.resetWireToBasis_pool]
  simp only [resetWireBudget, ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  have arranged :
      ResourcePool.singleton (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
        (ResourcePool.singleton (.gate (QuditShift.gateLabel (-path.1.2.1.toFin))) +
          ResourcePool.singleton (.gate (QuditShift.gateLabel (label wire)))) =
      (ResourcePool.singleton (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
        ResourcePool.singleton (.gate (QuditShift.gateLabel (label wire)))) +
          ResourcePool.singleton (.gate (QuditShift.gateLabel (-path.1.2.1.toFin))) := by ac_rfl
  exact arranged.le.trans (add_le_add le_rfl correction)

private theorem resetWire_depth_le {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) (duration : Resource.Event .quantum → Nat)
    (path : (QuditShift.resetWireToBasis wire output (label wire)).Path) :
    (QuditShift.resetWireToBasis wire output (label wire)).depth duration path ≤
      resetWireDepth wire label duration := by
  have correction : duration (.gate (QuditShift.gateLabel (-path.1.2.1.toFin))) ≤
      Finset.univ.sup (fun amount : Fin (ctx.quantumLayout.wire wire).dimension =>
        duration (.gate (QuditShift.gateLabel amount))) :=
    Finset.le_sup (f := fun amount : Fin (ctx.quantumLayout.wire wire).dimension =>
      duration (.gate (QuditShift.gateLabel amount))) (Finset.mem_univ _)
  exact Nat.add_le_add_right (Nat.add_le_add_left correction _) _

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)

/-- The actual wire order uses each finite correction branch and its original prescribed seed. -/
def samplingResetBudget : ResourcePool .quantum :=
  ∑ wire : Fin (PublicInput.terminal E exponentWidth).systemCount,
    resetWireBudget wire (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)

/-- Arbitrary durations use the largest possible correction at each physical position. -/
def samplingResetDepthLimit (duration : Resource.Event .quantum → Nat) : Nat :=
  ∑ wire : Fin (PublicInput.terminal E exponentWidth).systemCount,
    resetWireDepth wire (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed) duration

/-- The selected actual reset path lies within the literal finite branch allowance. -/
theorem samplingReset_pool_le
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).resourcePool path ≤
      samplingResetBudget E fieldTail exponentWidth sameWidth fits seed :=
  Circuit.forRange_pool_le_sum _ _ _
    (fun wire iteration => resetWire_pool_le wire (samplingResetCells E exponentWidth wire)
      (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed) iteration) path

/-- The complete arbitrary-duration bound follows the actual serial wire order. -/
theorem samplingReset_depth_le (duration : Resource.Event .quantum → Nat)
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).depth duration path ≤
      samplingResetDepthLimit E fieldTail exponentWidth sameWidth fits seed duration :=
  Circuit.forRange_depth_le_sum _ _ duration _
    (fun wire iteration => resetWire_depth_le wire (samplingResetCells E exponentWidth wire)
      (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed) duration iteration) path

/-- The true unit depth remains exactly three events per wire, regardless of branch allowance. -/
theorem samplingReset_unitDepth
    (path : (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path) :
    (samplingReset E fieldTail exponentWidth sameWidth fits seed).depth (fun _ => 1) path =
      3 * (PublicInput.terminal E exponentWidth).systemCount :=
  QuditShift.resetToBasisOn_unitDepth _ _ _ _ path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
