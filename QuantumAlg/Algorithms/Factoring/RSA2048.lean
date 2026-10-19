/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA2048.Recycling.Contract
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters

/-!
# Logical-resource estimate for the single-control RSA-2048 execution

The public modulus determines the actual new seven-batch execution. Its
proof-side original key model supplies distinct exact-width prime factors
and the good-key condition; neither factor is an executable input. The
complete mixed/reference state and borrowed obligations accompany its
independent native resources [EH17, source.tex:878-966;
E23, arxiv-v5.tex:218-299,329-355].
-/

namespace QuantumAlg.Factoring.RSA2048

noncomputable section

open EkeraHastadStyle.Canonical

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Complete native factoring at the fixed RSA-2048 width.

**Input.**
- The public modulus $N$ has an original proof-side good-key model with distinct
  odd exact $1024$-bit primes and an exact $2048$-bit product.
- Arbitrary normalized mixed caller states and external references are admitted;
  the actual program prepares its bank internally.
**Output.**
- The actual stored optional unsigned factor is accepted precisely when it is
  one of the original prime factors. All retained output cells remain present.
- Every output restores the single bank to its original seed jointly with the
  original external reference. Borrowed restoration is a separate obligation.
**Resource budget.**
- Seven complete batches execute 112 measured members, with 4,097 added qubits
  and 1,053,148,338,921 added classical bits in the simultaneous space allowance.
- The independent new native event pool includes preparation, both feedback
  streams, every reset/reload, paid packing, full recovery and final selection.
- It gives at most 117,064,166,104,596,480 Toffoli gates, 416,291,951,738,880
  CNOT gates, and 148,235,585 single-qubit gates.
- Quantum time is at most 117,480,458,204,112,193. All classical instructions
  remain charged: their count is at most 15,343,042,058,108,937,824.
- These numerical resource bounds hold for every original exact-width key,
  without a good-key premise; each peak adds the corresponding caller capacity.
**Success.**
- The original conditional seven-batch floor is at least $0.99$ on good keys.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
- Numerical native budgets refine this same actual single-control execution.
-/
public def problem (N : Nat) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (RSA.Recycling.Program.outputContext base noQuantum N NativeRSA2048.rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := NativeRSA2048.FixedKeyModel N
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun environment model =>
    (RSA.Recycling.Program.fixedRoundProblem base noQuantum N NativeRSA2048.rounds).accepts
      environment model.1
  successLB := fun environment model =>
    (RSA.Recycling.Program.fixedRoundProblem base noQuantum N NativeRSA2048.rounds).successLB
      environment model.1
  states := fun environment model =>
    (RSA.Recycling.Program.fixedRoundProblem base noQuantum N NativeRSA2048.rounds).states
      environment model.1
  resources :=
    (RSA.Recycling.Program.fixedRoundProblem base noQuantum N NativeRSA2048.rounds).resources
  quantumTimeLimit :=
    (RSA.Recycling.Program.fixedRoundProblem base noQuantum N NativeRSA2048.rounds).quantumTimeLimit

private lemma complete_correct {N : Nat} (specification : Input N) :
    (RSA.Recycling.Program.algorithm base noQuantum specification NativeRSA2048.rounds).Solves
      (problem base noQuantum N) := by
  have complete := RSA.Recycling.Program.rsaRecyclingParent_algorithm_solves_fixedRound
    base noQuantum specification NativeRSA2048.rounds
  constructor
  · intro environment model Reference input valid initialized
    exact complete.success environment model.1 Reference input valid initialized
  · intro environment model Reference input valid initialized requirement present
    exact complete.states environment model.1 Reference input valid initialized requirement present
  · intro environment model Reference input valid initialized
    exact complete.borrowed environment model.1 Reference input valid initialized
  · intro environment model Reference input valid initialized path supported
    exact complete.events environment model.1 Reference input valid initialized path supported
  · intro environment model Reference input valid initialized path supported
    exact complete.resident environment model.1 Reference input valid initialized path supported
  · intro environment model Reference input valid initialized path supported
    exact complete.auxiliary environment model.1 Reference input valid initialized path supported
  · intro environment model Reference input valid initialized path supported
    exact complete.time environment model.1 Reference input valid initialized path supported

/-- One actual seven-batch algorithm solves the independent fixed-width problem. -/
public theorem main {N : Nat} (specification : Input N) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (RSA.Recycling.Program.outputContext base noQuantum N NativeRSA2048.rounds)
      (LatticeBatchRecoveryOutput.OutputShape N),
      candidate.Solves (problem base noQuantum N) :=
  ⟨RSA.Recycling.Program.algorithm base noQuantum specification NativeRSA2048.rounds,
    complete_correct base noQuantum specification⟩

end

end QuantumAlg.Factoring.RSA2048
