/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage.Seed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Readout.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Store.Observation

/-!
# The actual allocated Shor readout transports complete reference weights

The packed result and all finite phase cells are initialized by the real
allocator. Its store push preserves every earlier operand, while the real
round reads the retained parameter and writes its actual phase result. Their
combined observation therefore uses the original store and the selected
compiled program's phase weights, with the whole reference entry preserved.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (ctx : RuntimeCtx .quantum) (N : Nat)

/-- The complete actual allocator's reference weight follows its real initialized store push. -/
theorem allocate_referenceFiberSum_store
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store (context ctx N) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate ctx N).execute Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (pushStore ctx N entry.1)) leftRef rightRef := by
  let allocationHead := Circuit.retain ctx ctx.canonicalFreshKey (.bits (phaseBits N))
    ctx.canonicalFreshKey_fresh
  let allocateCells := MeasurementCells.allocate (resultContext ctx N) 2 (phaseBits N)
  have sequence := Circuit.referenceFiberSum_execute_seq allocationHead allocateCells state weight
    leftRef rightRef
  have cells := MeasurementCells.allocate_referenceFiberSum_store (resultContext ctx N)
    2 (phaseBits N) (allocationHead.execute Reference state) weight leftRef rightRef
  exact sequence.trans (cells.trans
    (Circuit.referenceFiberSum_execute_retain ctx.canonicalFreshKey (.bits (phaseBits N))
      ctx.canonicalFreshKey_fresh state
      (fun store => weight (MeasurementCells.pushStore 2 (phaseBits N) store))
      leftRef rightRef))

/-- Allocation and the real selected round produce the joint old-input and phase observation. -/
theorem round_referenceFiberSum_input
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    {shape : CShape} (input : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : shape.Value → (CShape.bits (phaseBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((round ctx N sameWires parameter).execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput ctx N input))
          (entry.1.read (.storage (resultRef ctx N).toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => NativeQuantum.readoutWeight (entry.1.read parameter)
          (fun outcome => weight (entry.1.read input) (.bits outcome))) leftRef rightRef := by
  let quantumRound := NativeRound.code N ((quantumWires ctx N).trans sameWires)
    (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)
  let allocated := (allocate ctx N).execute Reference state
  let finalWeight := fun store : Store (context ctx N) =>
    weight (store.read (liftInput ctx N input))
      (store.read (.storage (resultRef ctx N).toCStorageRef))
  let inputWeight := fun store : Store (context ctx N) =>
    NativeQuantum.readoutWeight (store.read (liftInput ctx N parameter))
      (fun outcome => weight (store.read (liftInput ctx N input)) (.bits outcome))
  have sequence := Circuit.referenceFiberSum_execute_seq (allocate ctx N) quantumRound state
    finalWeight leftRef rightRef
  have measured := NativeRound.round_referenceFiberSum_input N
    ((quantumWires ctx N).trans sameWires) (liftInput ctx N parameter)
    (cells ctx N) (resultRef ctx N)
    (liftInput ctx N input) (cells_distinct ctx N) (cells_separate ctx N input)
    (result_separate ctx N input) allocated (allocate_seeded ctx N sameWires state seeded)
    weight leftRef rightRef
  refine sequence.trans (measured.trans
    ((allocate_referenceFiberSum_store ctx N state inputWeight leftRef rightRef).trans ?_))
  apply congrArg
    (fun observe : Store ctx × History → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry _
  dsimp only [inputWeight]
  rw [read_pushStore_liftInput, read_pushStore_liftInput]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeStorage
