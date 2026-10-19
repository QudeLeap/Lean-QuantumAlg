/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Simon.FixedSample.Model
public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Algorithms.Simon.FixedSample.Model
import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Resources
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent fixed-sample Simon specification

A fixed one-sample circuit is interpreted in an explicit oracle environment.
The source promise supplies only its Born-law certificate and hidden word. The independent finite
    budget charges one bank preparation,
every subsequent reset, the real terminal measurements and row packing, and
one polynomial GF(2) recovery. All surviving resources remain in the output.
-/

namespace QuantumAlg.SimonsProblem

open Execution FixedSample

noncomputable section

universe u

private lemma originalOutcome (n : Nat) : Outcome n = TerminalZMeasure.Outcome n := rfl

/-- No external quantum register or classical workspace is required by the sampler. -/
public def inputContext : RuntimeCtx .quantum := RuntimeCtx.empty

/-- The complete final context retains the one bank, all samples and the optional result. -/
public def outputContext (n : Nat) (κ : SecurityParameter) : RuntimeCtx .quantum :=
  Native.recoveryContext inputContext rfl n (sampleCount n κ)

/-- The original finite failure requirement for positive statistical slack. -/
@[expose] public def successLowerBound (κ : SecurityParameter) : ProbabilityLowerBound where
  value := 1 - ((2 : ENNReal)⁻¹) ^ κ.value
  le_one := tsub_le_self

/-- Independently fixed event coordinates and complete live-space allowances. -/
public def resourceBudget (n : Nat)
    (κ : SecurityParameter) : ResourceBudget (executionModel n) where
  events := Native.recoveryEnvelope n (sampleCount n κ)
  resident := Native.recoveryScratchSpace (sourceModel n) n (sampleCount n κ) +
    Native.samplingSpace n (sampleCount n κ)
  auxiliary := Native.recoveryScratchSpace (sourceModel n) n (sampleCount n κ) +
    Native.samplingSpace n (sampleCount n κ)

/-- Original member depth plus the paid reset, terminal and polynomial recovery stages. -/
public def depthLimit (n : Nat)
    (κ : SecurityParameter) : Nat :=
  Native.samplingDepthLimit n (sampleCount n κ) +
    ClassicalRoutines.GF2.Native.intoDepthLimit (model := executionModel n)
      (sampleCount n κ) n (fun _ => 1)

/-- Fixed-sample Simon with the original oracle promise and an actual retained output.

**Input.**
- A fixed one-sample circuit and an oracle interpretation whose original
  Born-law promise identifies a nonzero hidden mask. A positive slack `κ`
  fixes exactly `n + κ` samples. Every normalized local input and every
  external reference extension is admitted when the oracle promise holds.
**Output.**
- An optional machine word equal to the original hidden mask. The complete
  output also retains the physical bank and measured sample slots.
**Resource budget.**
- One preparation per bank qubit in a parallel layer; `n + κ` original members, each followed by
  `n` actual Z
  measurements and one row pack; `n + κ - 1` paid resets of the same `2n`
  bank; then one GF(2) recovery. Event envelopes include reset alternatives.
- Live storage includes every sample slot and finite readout cell, the one
  bank, the retained result and the maximum sequential scratch allowance.
  Auxiliary storage is included in resident storage.
- Unit native depth is `1 + (n + κ) * (n + 4) +
  (n + κ - 1) * 4n` plus the independent polynomial recovery depth limit.
**Success.**
- The hidden mask is returned with probability at least `1 - 2⁻κ`.
  No final zero-state promise or expected stopping rule is asserted.
**Source.**
- [dW19, qcnotes.tex:1407, 1409-1410].
- The fixed finite repetition uses the original Simon equation union bound.
-/
@[expose] public def problem {n : Nat} (sampling : SamplingCircuit n) (κ : SecurityParameter) :
    Problem (executionModel n) inputContext (outputContext n κ) (.option (.unsignedWord n)) where
  Witness := Word n
  valid := fun environment secret _ => SamplingPromise sampling environment.quantum secret
  initialization := fun _ _ _ => True
  accepts := fun _ secret _ output => output = .optionSome (.unsignedWord secret)
  successLB := fun _ _ => successLowerBound κ
  states := fun _ _ => []
  resources := resourceBudget n κ
  quantumTimeLimit := depthLimit n κ

/-- The original source promise admits the already fixed circuit in the same environment. -/
public lemma simon_problem_source_valid {n : Nat} (sampling : SamplingCircuit n)
    (κ : SecurityParameter) (environment : (executionModel n).Environment)
    {α : Type u} {f : Simon.Oracle n α} {secret : Simon.BitVec n}
    (source : Model sampling environment.quantum f secret) (promise : Simon.Promise f secret)
    (state : ExecutionState (Store inputContext) inputContext.register) :
    (problem sampling κ).valid environment source.secret state :=
  model_samplingPromise source promise

end

end QuantumAlg.SimonsProblem
