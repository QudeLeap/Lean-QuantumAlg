/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Packed.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Readout.Weight

/-!
# Actual Shor phase readout jointly with the earlier structural input

The actual phase writes and packing preserve all earlier input cells on
their separate physical storage keys. Their joint final observation is
therefore the earlier value weighted by the selected program's actual phase
amplitudes. The allocating caller proves separation from its real fresh keys.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual joint earlier-input and packed-phase weight retains its full reference entry. -/
theorem round_referenceFiberSum_input {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    {shape : CShape} (input : CInputRef ctx shape)
    (distinct : Function.Injective (fun index => (cells index).key))
    (cellsSeparate : ∀ index, (cells index).key ∉ input.storageKeys)
    (resultSeparate : result.key ∉ input.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : shape.Value → (CShape.bits (phaseBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((code N sameWires parameter cells result).execute Reference state)
        (fun entry _ => weight (entry.1.read input)
          (entry.1.read (.storage result.toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => NativeQuantum.readoutWeight (entry.1.read parameter)
          (fun outcome => weight (entry.1.read input) (.bits outcome))) leftRef rightRef := by
  refine (round_referenceFiberSum_seeded N sameWires parameter cells result state seeded
    (fun store => weight (store.read input) (store.read (.storage result.toCStorageRef)))
    leftRef rightRef).trans ?_
  apply congrArg
    (fun observe : Store ctx × History → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry _
  refine Eq.trans ?_ (NativePlacement.readoutWeight_coordinates N sameWires
    (entry.1.read parameter) (fun outcome => weight (entry.1.read input) (.bits outcome)))
  apply Finset.sum_congr rfl
  intro basis _
  rw [packed_read_preserved N sameWires cells result input cellsSeparate resultSeparate,
    packed_output N sameWires cells result distinct]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
