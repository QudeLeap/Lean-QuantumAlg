/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Persistent
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Reuse
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialization

/-!
# Actual initial storage, single-bank preparation and first complete Shor round

The producer allocates and clears its own first-success storage, prepares one
real zero bank, then executes complete sampling, native recovery, feedback and
physical reset. The incoming state supplies neither selector cells, success
values nor a prepared bank. The next sample consumes the entire actual output.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

include noQuantum in
/-- The actual retained initializer preserves the empty incoming quantum carrier. -/
lemma noQuantumStorage : (Persistent.context base N).quantumWires = [] :=
  (Persistent.quantumWires base N).trans noQuantum

/-- Precisely one actual bank is added after the genuine persistent allocations. -/
def bank : RuntimeCtx .quantum :=
  bankContext (Persistent.context base N) (noQuantumStorage base noQuantum N) N

/-- Quantum preparation preserves each real writable persistent storage identity. -/
def liftWrite {shape : CShape} (cell : CWriteRef (Persistent.context base N) shape) :
    CWriteRef (bank base noQuantum N) shape where
  toCStorageRef := cell.toCStorageRef.underOwnedLayout
    (Persistent.context base N).canonicalFreshKey (layout N)
    (Persistent.context base N).canonicalFreshKey_fresh
    (allocationDisjoint (Persistent.context base N) (noQuantumStorage base noQuantum N) N)
  writable := cell.writable

/-- The actual initializer's four selector cells survive preparation on the same keys. -/
def cells : NativeFactorScan.Cells (bank base noQuantum N) N where
  candidate := liftWrite base noQuantum N (Persistent.candidateRef base N)
  accepted := liftWrite base noQuantum N (Persistent.acceptedRef base N)
  selected := liftWrite base noQuantum N (Persistent.selectedRef base N)
  scratch := liftWrite base noQuantum N (Persistent.scratchRef base N)

/-- The real optional result remains the only destination for final paid packing. -/
def result : CWriteRef (bank base noQuantum N) (.option (.unsignedWord (modulusBits N))) :=
  liftWrite base noQuantum N (Persistent.resultRef base N)

/-- The producer's actual bank has exactly the declared member's physical wire list. -/
lemma bank_wires : (bank base noQuantum N).quantumWires = (layout N).wires :=
  bankContext_wires (Persistent.context base N) (noQuantumStorage base noQuantum N) N

variable (input : Input N)

variable {environment : (executionModel N).Environment}

/-- Genuine retained allocation and Boolean clearing precede the one real zero preparation. -/
def ready : Circuit (executionModel N) base (bank base noQuantum N) :=
  (Persistent.initialization (model := executionModel N) base N).seq
    (Sampling.prepare (Persistent.context base N) (noQuantumStorage base noQuantum N) N)

/-- The first complete round consumes that actual initialization, with no extra seed witness. -/
def code : Circuit (executionModel N) base
    (Iteration.context (bank base noQuantum N) N) :=
  (ready base noQuantum N).seq
    (Completion.code (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N))

/-- Observe both actual persistent latches and retain every live source and caller entry. -/
def run : AlgorithmRun (executionModel N) base
    (Iteration.context (bank base noQuantum N) N) (.product .bit (.unsignedWord (modulusBits N)))
      where
  code := code base noQuantum N input
  output := Output.all (Iteration.context (bank base noQuantum N) N)
    (.read (.product
      (.storage (Completion.cells (bank base noQuantum N) N
        (cells base noQuantum N)).accepted.toCStorageRef)
      (.storage (Completion.cells (bank base noQuantum N) N
        (cells base noQuantum N)).selected.toCStorageRef)))

/-- Actual initialization supplies zero in every complete store and reference block. -/
lemma ready_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History)) :
    BasisSeeded.Holds (bank base noQuantum N).quantumLayout.zeroLabel
      ((ready base noQuantum N).execute environment Reference state) :=
  BasisSeeded.seq
    (environment := environment) (Persistent.initialization (model := executionModel N) base N)
    (Sampling.prepare (Persistent.context base N) (noQuantumStorage base noQuantum N) N)
    _ state
    (sampling_prepare_seeded
      (environment := environment) (Persistent.context base N) (noQuantumStorage base noQuantum N)
      N ((Persistent.initialization (model := executionModel N) base N).execute
        environment Reference state))

/-- The actual first complete round finishes with that same original bank in physical zero. -/
lemma code_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History)) :
    BasisSeeded.Holds (Iteration.context (bank base noQuantum N) N).quantumLayout.zeroLabel
      ((code base noQuantum N input).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (ready base noQuantum N)
    (Completion.code (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N)) _ state
    (Completion.code_seeded (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N)
      ((ready base noQuantum N).execute environment Reference state))

/-- Every reference coordinate of the next sample uses the entire actual first-round output. -/
lemma next_source_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel N).HiddenState × History))
    (outcome : SourceOutcome N) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Iteration.code (Iteration.context (bank base noQuantum N) N) N
        ((Iteration.quantumWires (bank base noQuantum N) N).trans
          (bank_wires base noQuantum N))).execute (Runtime.environment input) Reference
            ((code base noQuantum N input).execute (Runtime.environment input) Reference state))
      (fun entry _ => if sourceRead (Iteration.context (bank base noQuantum N) N) N entry.1 =
        outcome
        then 1 else 0) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((code base noQuantum N input).execute (Runtime.environment input) Reference state)
        (fun _ _ => ((sourceOutcomePMF input outcome).toReal : ℂ)) leftRef rightRef :=
  iteration_source_reference (Iteration.context (bank base noQuantum N) N) N input
    ((Iteration.quantumWires (bank base noQuantum N) N).trans (bank_wires base noQuantum N))
    ((code base noQuantum N input).execute (Runtime.environment input) Reference state)
    (code_seeded
      (environment := Runtime.environment input) base noQuantum N input state)
    outcome leftRef rightRef

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
