/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
public import
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
public import
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA2048.Measured.Contract
import all QuantumAlg.Algorithms.Factoring.RSA2048.Measured.Success.Relational
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters

/-!
# Logical-resource estimate for the single-control RSA-2048 execution

The public modulus determines the actual new four-batch execution. Its
proof-side original key model supplies distinct exact-width prime factors
and the good-key condition; neither factor is an executable input. The
complete mixed/reference state and borrowed obligations accompany its
independent native resources [EH17, source.tex:878-966;
E23, arxiv-v5.tex:218-299,329-355].
-/

namespace QuantumAlg.Factoring.RSA2048

noncomputable section

attribute [local instance] RSA.Configuration.rsa2048

attribute [local irreducible] RSA.Measured.Program.outputContext
  RSA.Measured.Program.stateRequirement

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
- Four complete batches execute 80 measured members, with 4,100 added qubits
  and 1,053,148,158,593 added classical bits in the simultaneous space allowance.
- The independent new native event pool includes preparation, both feedback
  streams, every reset/reload, paid packing, full recovery and final selection.
- It gives at most 19,254,517,596,160 Toffoli gates, 74,265,936,855,040
  CNOT gates, and 16,506,186,343,601 single-qubit gates.
- Actual physical measurements have a separate ceiling of 2,750,117,806,640.
- Quantum time is at most 110,026,640,794,801. All classical instructions
  remain charged: their count is at most 13,881,799,957,336,389,973.
- These numerical resource bounds hold for every original exact-width key,
  without a good-key premise; each peak adds the corresponding caller capacity.
**Success.**
- The original conditional four-batch floor is at least $0.99$ on good keys.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
- [G25, main.tex:199-295,354-360] supplies measured arithmetic; the independent
  polynomial native allowances are derived from this actual emitted program.
- The quantum-time ceiling is weighted native work above the actual schedule,
  without an optimal-depth claim. Classical and quantum coordinates stay separate.
-/
public def problem (N : Nat) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (RSA.Measured.Program.outputContext base noQuantum N RSA.Configuration.rsa2048Batches)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Measured.refineProblem
    (RSA.Measured.Program.fixedRoundProblem base noQuantum N RSA.Configuration.rsa2048Batches)
    (fun model : NativeRSA2048.FixedKeyModel N => model.1)
    (fun _ _ => Measured.conditionalSuccessFloor)

private lemma complete_correct {N : Nat} (specification : Input N) :
    (RSA.Measured.Program.algorithm base noQuantum specification
      RSA.Configuration.rsa2048Batches).Solves
      (problem base noQuantum N) := by
  unfold problem
  apply Measured.solves_refineProblem _ _ _
    (RSA.Measured.Program.rsaMeasuredParent_algorithm_solves_fixedRound
      base noQuantum specification RSA.Configuration.rsa2048Batches)
  intro environment model Reference input valid initialized
  exact Measured.rsaMeasured2048_relational_twentyByFour_success_ge_99
    base noQuantum specification model input

/-- One actual four-batch algorithm solves the independent fixed-width problem. -/
public theorem main {N : Nat} (specification : Input N) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (RSA.Measured.Program.outputContext base noQuantum N RSA.Configuration.rsa2048Batches)
      (LatticeBatchRecoveryOutput.OutputShape N),
      candidate.Solves (problem base noQuantum N) :=
  ⟨RSA.Measured.Program.algorithm base noQuantum specification RSA.Configuration.rsa2048Batches,
    complete_correct base noQuantum specification⟩

end

end QuantumAlg.Factoring.RSA2048
