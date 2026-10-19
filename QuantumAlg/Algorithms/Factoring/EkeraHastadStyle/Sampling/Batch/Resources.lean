/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Resources
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-!
# Native first-batch budgets with one real preparation

The independent allowance contains the complete residue sampler, one zero
preparation per physical bank wire, its literal seed-loading X word and
sixteen complete measured rounds. It preserves all native gate coordinates
and charges packing, reset and reload. Actual
measurement-cell retention emits no event; its live capacity is accounted for
separately. The one preparation is outside the repeated-round constructor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution
open ShortDLP.CompiledMAU

/-- Independent native coordinate allowance for the complete first shared-generator batch. -/
def nativeEnvelope (N : Nat) : ResourcePool RuntimeRound.model :=
  (ShorStyle.Canonical.Sampler.Retained.nativeEnvelope RuntimeRound.model N +
    (ShortDLP.totalQubits
      (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) •
      ResourcePool.singleton (model := RuntimeRound.model) (.preparation (2 : ℕ+)) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N •
        ResourcePool.singleton (model := RuntimeRound.model) (.gate .singleQubit))) +
    16 • RuntimeRound.eventEnvelope (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- Independent depth counts parallel zero preparation, literal loading, and sixteen real rounds. -/
def unitDepthBound (N : Nat) : Nat :=
  (44 * modulusBits N + 161 +
    ((if ShortDLP.totalQubits
        (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) = 0
        then 0 else 1) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)) +
    16 * RuntimeRound.unitDepthBound (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

private lemma sequence_pool {pre middle post : RuntimeCtx .quantum}
    (first : Circuit RuntimeRound.model pre middle)
    (second : Circuit RuntimeRound.model middle post)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 :=
  ResourcePool.ofList_append _ _

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The literal first-batch path obeys the independent allowance at every native coordinate. -/
lemma nativeBatch_resourcePool_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).resourcePool path ≤ nativeEnvelope N := by
  let sampler : Circuit RuntimeRound.model base (sampledContext base N) :=
    ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N
  let prepare : Circuit RuntimeRound.model
      (sampledContext base N) (bankContext base noQuantum N) :=
    RuntimeBank.prepare (operations := BitWord.model) (services := .empty) (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  let allocate : Circuit RuntimeRound.model
      (bankContext base noQuantum N) (readyContext base noQuantum N) :=
    MeasurementCells.allocate (model := RuntimeRound.model)
      (bankContext base noQuantum N) 2 (measurementBits N)
  have prepared : prepare.resourcePool path.1.1.2 =
      ShortDLP.totalQubits
        (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) •
        ResourcePool.singleton (model := RuntimeRound.model) (.preparation (2 : ℕ+)) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N •
        ResourcePool.singleton (model := RuntimeRound.model) (.gate .singleQubit) :=
    RuntimeBank.shortDLP_runtimeBank_prepare_resourcePool
      (operations := BitWord.model) (services := .empty) (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N path.1.1.2
  have allocated : allocate.resourcePool path.1.2 = 0 :=
    congrArg ResourcePool.ofList
      (MeasurementCells.allocate_eventTrace (model := RuntimeRound.model)
        (bankContext base noQuantum N)
        2 (measurementBits N) path.1.2)
  have first : (sampleAndPrepare base noQuantum N).resourcePool path.1.1 ≤
      ShorStyle.Canonical.Sampler.Retained.nativeEnvelope RuntimeRound.model N +
        (ShortDLP.totalQubits
          (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) •
          ResourcePool.singleton (model := RuntimeRound.model) (.preparation (2 : ℕ+)) +
          reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N •
            ResourcePool.singleton (model := RuntimeRound.model) (.gate .singleQubit)) :=
    (sequence_pool sampler prepare path.1.1).le.trans
      (add_le_add
        (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le
          (model := RuntimeRound.model) base N path.1.1.1)
        prepared.le)
  have initialized : (initializeBank base noQuantum N).resourcePool path.1 ≤
      ShorStyle.Canonical.Sampler.Retained.nativeEnvelope RuntimeRound.model N +
        (ShortDLP.totalQubits
          (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) •
          ResourcePool.singleton (model := RuntimeRound.model) (.preparation (2 : ℕ+)) +
          reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N •
            ResourcePool.singleton (model := RuntimeRound.model) (.gate .singleQubit)) := by
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
lemma nativeBatch_unitDepth_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).depth (fun _ => 1) path ≤ unitDepthBound N := by
  have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_unit_depth_le
    (model := RuntimeRound.model) base N path.1.1.1
  have repeated := RuntimeRepetition.shortDLP_runtimeRepetition_unitDepth_le
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
    (parameter base noQuantum N) (cells base noQuantum N) 16 path.2
  have allocated := MeasurementCells.allocate_depth (model := RuntimeRound.model)
    (bankContext base noQuantum N)
    2 (measurementBits N) (fun _ => 1) path.1.2
  have prepared : (RuntimeBank.prepare (operations := BitWord.model) (services := .empty)
      (sampledContext base N) (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).depth
        (fun _ => 1) path.1.1.2 =
      (if ShortDLP.totalQubits
          (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) = 0
        then 0 else 1) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N := by
    have evaluated := congrArg
      (DepthExpr.depthEval (fun _ : Resource.Event RuntimeRound.model => 1))
      (RuntimeBank.shortDLP_runtimeBank_prepare_eventDepth
        (operations := BitWord.model) (services := .empty) (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N path.1.1.2)
    refine evaluated.trans ?_
    exact (DepthExpr.depthEval_seq _ _ _).trans (congrArg₂ Nat.add
      (ZeroPreparation.zeroPreparation_unit_depth AlgorithmGate.model .empty
        (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) BitWord.model .empty)
      ((UnitaryCircuit.unitaryCircuit_unit_depth_classical_context
        (reloadProgram (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
        BitWord.model .empty).trans
        (shortDLP_reload_unitDepth (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)))
  have actual : (code base noQuantum N).depth (fun _ => 1) path =
      ((ShorStyle.Canonical.Sampler.Retained.circuit (model := RuntimeRound.model) base N).depth
        (fun _ => 1) path.1.1.1 +
      (RuntimeBank.prepare (operations := BitWord.model) (services := .empty)
        (sampledContext base N) (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).depth
          (fun _ => 1) path.1.1.2 +
      (MeasurementCells.allocate (model := RuntimeRound.model)
        (bankContext base noQuantum N) 2 (measurementBits N)).depth
        (fun _ => 1) path.1.2) + (rounds base noQuantum N).depth (fun _ => 1) path.2 := rfl
  refine actual.le.trans ?_
  calc
    _ ≤ _ := Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add sampled prepared.le) allocated.le) repeated
    _ = unitDepthBound N := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
