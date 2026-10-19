/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Seed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Layout.Separation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Moments

/-!
# The actual sixteen-round batch has the original conditional vector distribution

The real sampler, one bank preparation and finite-cell allocations establish
the seed. The actual sixteen rounds then have the original independent vector
PMF conditioned on the parameter read from that very retained store. Every
finite joint weight may also observe earlier sampled data, and every reference
matrix coordinate is retained. No independence or initialization premise is
required of the incoming state.

This is the complete conditional quantum-batch identity. Its input-side state
is the actual initialization execution, so subsequent sampling pushforward
proofs must retain the original sampler distribution and source data.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open ShortDLP.CompiledMAU
open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The actual rounds have the original conditional vector PMF in every reference coordinate. -/
lemma nativeBatch_rounds_weighted_reference {previousShape : CShape}
    (previous : CInputRef (sampledContext base N) previousShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N) Reference
      (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (nativeBatch_ready_wires base noQuantum N) N state)
    (weight : (ParameterShape N).Value → previousShape.Value →
      (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((rounds base noQuantum N).execute environment Reference state)
        (fun entry _ => weight (entry.1.read (finalParameter base noQuantum N))
          (entry.1.read (finalInput base noQuantum N previous))
          (entry.1.read (finalResults base noQuantum N)).get) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
          ((PMF.independentReplicateVector
            ((ShortDLP.measurement (ShortDLP.CompiledMAU.registerParameters
              (shortLogBits N) (tradeoffBits N) (arithmeticBits N))).outcomePMF
              (evolvedState (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
                (parameterUnit (entry.1.read (parameter base noQuantum N)))
                (parameterTarget (entry.1.read (parameter base noQuantum N))))) 16 samples).toReal :
                  ℂ) * weight (entry.1.read (parameter base noQuantum N))
                    (entry.1.read (readyInput base noQuantum N previous))
                    (fun index => .bits (samples.get index))) leftRef rightRef :=
  RuntimeRepetition.shortDLP_runtimeRepetition_weighted_reference
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
    (parameterUnit (N := N)) (parameterTarget (N := N)) 16
    (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
    (parameter base noQuantum N) (readyInput base noQuantum N previous)
    (cells base noQuantum N) (nativeBatch_cells_distinct base noQuantum N)
    (nativeBatch_cells_parameter_separate base noQuantum N previous)
    state seeded weight leftRef rightRef

/-- Complete actual initialization supplies the seed for the same-state sixteen-round identity. -/
lemma nativeBatch_complete_weighted_reference {previousShape : CShape}
    (previous : CInputRef (sampledContext base N) previousShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (weight : (ParameterShape N).Value → previousShape.Value →
      (Fin 16 → (CShape.bits (measurementBits N)).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((code base noQuantum N).execute environment Reference state)
        (fun entry _ => weight (entry.1.read (finalParameter base noQuantum N))
          (entry.1.read (finalInput base noQuantum N previous))
          (entry.1.read (finalResults base noQuantum N)).get) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((initializeBank base noQuantum N).execute environment Reference state)
        (fun entry _ => ∑ samples : List.Vector (Fin (measurementBits N) → Bool) 16,
          ((PMF.independentReplicateVector
            ((ShortDLP.measurement (ShortDLP.CompiledMAU.registerParameters
              (shortLogBits N) (tradeoffBits N) (arithmeticBits N))).outcomePMF
              (evolvedState (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
                (parameterUnit (entry.1.read (parameter base noQuantum N)))
                (parameterTarget (entry.1.read (parameter base noQuantum N))))) 16 samples).toReal :
                  ℂ) * weight (entry.1.read (parameter base noQuantum N))
                    (entry.1.read (readyInput base noQuantum N previous))
                    (fun index => .bits (samples.get index))) leftRef rightRef :=
  (Circuit.referenceFiberSum_execute_seq (environment := environment)
    (initializeBank base noQuantum N)
    (rounds base noQuantum N) state
    (fun store => weight (store.read (finalParameter base noQuantum N))
      (store.read (finalInput base noQuantum N previous))
      (store.read (finalResults base noQuantum N)).get) leftRef rightRef).trans
    (nativeBatch_rounds_weighted_reference base noQuantum N previous
      ((initializeBank base noQuantum N).execute environment Reference state)
      (nativeBatch_initializeBank_seedBlocks base noQuantum N state) weight leftRef rightRef)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
