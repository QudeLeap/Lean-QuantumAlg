/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Success
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Space
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Independent complete Shor sampling and recovery protocol

The input domain sees only local joint blocks. Positive records may contain
an absent latch or a factor of the original unknown-prime semiprime. All
external reference extensions remain admitted. The complete protocol includes
source sampling, the declared query, native recovery, first-success feedback
and physical reset before any subsequent quantum round.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round

open Execution

noncomputable section

/-- Observe the existing accepted bit and selected word without a new instruction. -/
def resultRead (ctx : RuntimeCtx .quantum) (N : Nat) (cells : NativeFactorScan.Cells ctx N) :
    OutputRead (Iteration.context ctx N) (.product .bit (.unsignedWord (modulusBits N))) :=
  .read (.product (.storage (Completion.cells ctx N cells).accepted.toCStorageRef)
    (.storage (Completion.cells ctx N cells).selected.toCStorageRef))

/-- The real two-cell result denotes a factor of the original mathematical instance. -/
def accepts {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (value : (CShape.product .bit (.unsignedWord (modulusBits N))).Value) : Prop :=
  Probability.ReturnedDeclaredFactor model (CShape.packOption value)

/-- Zero bank support and sound incoming latches are properties of local joint state alone. -/
def inputDomain (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (cells : NativeFactorScan.Cells ctx N)
    (state : ExecutionState
      (Store ctx × (executionModel N).HiddenState)
      ctx.register) : Prop :=
  (∀ entry basis, basis ≠ ctx.quantumLayout.zeroLabel →
    (state.block entry).matrix basis basis = 0) ∧
  (∀ entry, 0 < (state.block entry).mass →
    SoundLatch model (NativeFactorScan.latchValue cells entry.1))

/-- Every actual output fiber has the same predetermined full physical zero bank. -/
def stateRequirement (ctx : RuntimeCtx .quantum) (N : Nat) (cells : NativeFactorScan.Cells ctx N) :
    StateRequirement ctx (Iteration.context ctx N) :=
  .marginal Finset.univ (resultRead ctx N cells)
    (fun _ _ => .pure (NormalizedVector.ket
      ((Iteration.context ctx N).quantumLayout.restrictSelectedBasis Finset.univ
        (Iteration.context ctx N).quantumLayout.zeroLabel)))

/-- One independent complete declared-query factorization attempt.

**Input.**
- The original modulus and a zero physical bank, with an absent or sound
  persistent latch; arbitrary joint service and external reference extensions.
**Output.**
- The actual accepted bit and selected word, all retained source results,
  the same physical zero bank and every restored borrowed correlation.
**Resource budget.**
- The complete source sampler, one modular-exponentiation query, inverse
  Fourier gates, real phase measurements, bit packing, full native factor
  recovery, first-success feedback and paid reset of the whole bank.
- Caller capacity, every retained result and simultaneous native scratch are
  included in both space ledgers. Depth uses the same actual dependency path
  under the canonical quantum duration and the independent event allowance.
**Success.**
- The original rational one-attempt floor for a factor of the unknown-prime
  semiprime, including even moduli and all sampled nonunit parameters.
**Source.**
- [Sho95, source.tex:1124-1169,1183-1245] for sampling and factor recovery.
- [dW19, qcnotes.tex:2203-2225] for the declared XOR query interpretation.
-/
def problem (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (cells : NativeFactorScan.Cells ctx N) :
    Problem (executionModel N) ctx
      (Iteration.context ctx N) (.product .bit (.unsignedWord (modulusBits N))) where
  Witness := NumberTheory.Factoring.SemiprimeFactorModel N
  valid := fun actual _ _ => actual.quantum =
    DeclaredSource.interpretation (sourceBounds input) (phaseBits N)
  initialization := fun _ witness => inputDomain ctx witness cells
  accepts := fun _ witness _ value => accepts witness value
  successLB := fun _ _ => ⟨Probability.honestAttemptSuccessFloor N, honestFloor_le_one input⟩
  states := fun _ _ => [stateRequirement ctx N cells]
  resources :=
    { events := completionEnvelope N
      resident := ctx.residentSpace + completionAdditionalSpace N
      auxiliary := ctx.auxiliarySpace + completionAdditionalSpace N }
  quantumTimeLimit := ResourcePool.weightedCount Resource.Event.quantumDuration
    (completionEnvelope N)

/-- The actual complete round depends only on the public modulus and its nontriviality proof. -/
def algorithm (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    Algorithm (executionModel N) ctx
      (Iteration.context ctx N) (.product .bit (.unsignedWord (modulusBits N))) where
  run := Completion.run ctx N input sameWires cells result

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round
