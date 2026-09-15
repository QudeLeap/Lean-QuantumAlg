/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Resources

/-!
# Native first-batch budgets with one real preparation

The independent allowance contains the complete residue sampler, one native
source-seed preparation and sixteen complete measured rounds. It preserves
all controlled gate coordinates and charges packing, reset and reload. Actual
measurement-cell retention emits no event; its live capacity is accounted for
separately. The one preparation is outside the repeated-round constructor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution
open ShortDLP.CompiledMAU

/-- Independent native coordinate allowance for the complete first shared-generator batch. -/
def nativeEnvelope (N : Nat) : ResourcePool .quantum :=
  (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N +
    ResourcePool.singleton
      (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event) +
    16 • RuntimeRound.eventEnvelope (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- Independent unit-duration bound includes one preparation before the sixteen actual rounds. -/
def unitDepthBound (N : Nat) : Nat :=
  (44 * modulusBits N + 161 + 1) +
    16 * RuntimeRound.unitDepthBound (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

private theorem sequence_pool {pre middle post : RuntimeCtx .quantum}
    (first : Circuit pre middle) (second : Circuit middle post)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 :=
  ResourcePool.ofList_append _ _

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The literal first-batch path obeys the independent allowance at every native coordinate. -/
theorem nativeBatch_resourcePool_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).resourcePool path ≤ nativeEnvelope N := by
  let sampler : Circuit base (sampledContext base N) :=
    ShorStyle.Canonical.Sampler.Retained.circuit base N
  let prepare : Circuit (sampledContext base N) (bankContext base noQuantum N) :=
    RuntimeBank.prepare (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  let allocate : Circuit (bankContext base noQuantum N) (readyContext base noQuantum N) :=
    MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)
  have prepared : prepare.resourcePool path.1.1.2 =
      ResourcePool.singleton
        (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event :=
    congrArg ResourcePool.ofList
      (RuntimeBank.shortDLP_runtimeBank_prepare_eventTrace (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N path.1.1.2)
  have allocated : allocate.resourcePool path.1.2 = 0 :=
    congrArg ResourcePool.ofList
      (MeasurementCells.allocate_eventTrace (bankContext base noQuantum N)
        2 (measurementBits N) path.1.2)
  have first : (sampleAndPrepare base noQuantum N).resourcePool path.1.1 ≤
      ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N +
        ResourcePool.singleton
          (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event :=
    (sequence_pool sampler prepare path.1.1).le.trans
      (add_le_add
        (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le base N path.1.1.1)
        prepared.le)
  have initialized : (initializeBank base noQuantum N).resourcePool path.1 ≤
      ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N +
        ResourcePool.singleton
          (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event := by
    refine (sequence_pool (sampleAndPrepare base noQuantum N) allocate path.1).le.trans ?_
    exact (add_le_add first allocated.le).trans_eq (add_zero _)
  exact (sequence_pool (initializeBank base noQuantum N) (rounds base noQuantum N) path).le.trans
    (add_le_add initialized
      (RuntimeRepetition.shortDLP_runtimeRepetition_resourcePool_le
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
        (parameterUnit (N := N)) (parameterTarget (N := N))
        (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
        (parameter base noQuantum N) (cells base noQuantum N) 16 path.2))

/-- The same real instruction path counts preparation and every complete measured round in depth. -/
theorem nativeBatch_unitDepth_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).depth (fun _ => 1) path ≤ unitDepthBound N := by
  have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_unit_depth_le
    base N path.1.1.1
  have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_unitDepth_le
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
    (parameter base noQuantum N) (cells base noQuantum N) 16 path.2
  have allocated := MeasurementCells.allocate_depth (bankContext base noQuantum N)
    2 (measurementBits N) (fun _ => 1) path.1.2
  have actual : (code base noQuantum N).depth (fun _ => 1) path =
      ((ShorStyle.Canonical.Sampler.Retained.circuit base N).depth
        (fun _ => 1) path.1.1.1 + 1 +
      (MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)).depth
        (fun _ => 1) path.1.2) + (rounds base noQuantum N).depth (fun _ => 1) path.2 := rfl
  refine actual.le.trans ?_
  calc
    _ ≤ _ := Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add_right sampled 1) allocated.le) repeated
    _ = unitDepthBound N := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
