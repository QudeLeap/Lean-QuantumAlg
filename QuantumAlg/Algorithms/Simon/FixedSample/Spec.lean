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

The original one-sample circuit and Born-law certificates determine the
source instance. The independent finite budget charges one bank preparation,
every subsequent reset, the real terminal measurements and row packing, and
one polynomial GF(2) recovery. All surviving resources remain in the output.
-/

namespace QuantumAlg.SimonsProblem

open Execution FixedSample

noncomputable section

universe u

private theorem originalOutcome (n : Nat) : Outcome n = TerminalZMeasure.Outcome n := rfl

/-- No external quantum register or classical workspace is required by the sampler. -/
public def inputContext : RuntimeCtx .quantum := RuntimeCtx.empty

/-- The complete final context retains the one bank, all samples and the optional result. -/
public def outputContext (n : Nat) (κ : SecurityParameter) : RuntimeCtx .quantum :=
  Native.recoveryContext inputContext rfl n (sampleCount n κ)

/-- The original finite failure requirement for positive statistical slack. -/
def successLowerBound (κ : SecurityParameter) : ProbabilityLowerBound where
  value := 1 - ((2 : ENNReal)⁻¹) ^ κ.value
  le_one := tsub_le_self

/-- Independently fixed event coordinates and complete live-space allowances. -/
def resourceBudget {n : Nat} (oracle : UnitaryOperator (Qubits (2 * n)))
    (κ : SecurityParameter) : ResourceBudget (executionModel oracle) where
  events := Native.recoveryEnvelope oracle (sampleCount n κ)
  resident := Native.recoveryScratchSpace (sourceModel oracle) n (sampleCount n κ) +
    Native.samplingSpace n (sampleCount n κ)
  auxiliary := Native.recoveryScratchSpace (sourceModel oracle) n (sampleCount n κ) +
    Native.samplingSpace n (sampleCount n κ)

/-- Original member depth plus the paid reset, terminal and polynomial recovery stages. -/
def depthLimit {n : Nat} (oracle : UnitaryOperator (Qubits (2 * n)))
    (κ : SecurityParameter) : Nat :=
  Native.samplingDepthLimit n (sampleCount n κ) +
    ClassicalRoutines.GF2.Native.intoDepthLimit (model := executionModel oracle)
      (sampleCount n κ) n (fun _ => 1)

/-- Fixed-sample Simon with the original oracle promise and an actual retained output.

**Input.**
- The original Simon oracle, nonzero hidden mask and concrete one-sample
  circuit with its original Born-law certificates. A positive slack `κ`
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
public def problem {n : Nat} {α : Type u} {f : Simon.Oracle n α}
    {secret : Simon.BitVec n} (model : Model f secret) (κ : SecurityParameter) :
    Problem (executionModel model.sampling.oracle) inputContext (outputContext n κ) (.option
      (.unsignedWord n)) where
  valid := fun _ => Simon.Promise f secret
  initialization := fun _ => True
  accepts := fun _ output => output = .optionSome (.unsignedWord model.secret)
  successLB := successLowerBound κ
  states := []
  resources := resourceBudget model.sampling.oracle κ
  depth := {
    duration := fun _ => 1
    limit := depthLimit model.sampling.oracle κ
    classicalQuery_unit := fun _ => rfl
    quantumQuery_unit := fun _ => rfl
  }

end

end QuantumAlg.SimonsProblem
