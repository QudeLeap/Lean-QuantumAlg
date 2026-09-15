/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Layout.Separation
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Actual public-modulus loading followed by the source proposal scan

This composition loads the public modulus with literal native instructions,
then scans the original sixteen addressed proposals in the actual eleven-cell
layout. Its complete state equation holds on arbitrary inner stores.
Initialization is supplied by the real lexical pushes at the enclosing
boundary, without requiring workspace initialization from the caller.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Scan

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Load the public modulus in its real extended word before any interval test. -/
def loader (ctx : RuntimeCtx kind) (N : Nat) :
    Circuit (Layout.context ctx (modulusBits N)) (Layout.context ctx (modulusBits N)) :=
  ConstantWord.circuit (Layout.modulusCell ctx (modulusBits N)) N

/-- Execute the actual modulus loader and the original ordered proposal scan. -/
def circuit (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N))) :
    Circuit (Layout.context ctx (modulusBits N)) (Layout.context ctx (modulusBits N)) :=
  .seq (loader ctx N)
    (Proposal.scan (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N)))

/-- Store and literal path of the real public-modulus loader. -/
def loaderStep (N : Nat) (store : Store (Layout.context ctx (modulusBits N))) :
    Store (Layout.context ctx (modulusBits N)) × (loader ctx N).Path :=
  ConstantWord.foldStep (Layout.modulusCell ctx (modulusBits N))
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) store

private theorem loader_execute (N : Nat) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Layout.context ctx (modulusBits N)) Reference History) :
    (loader ctx N).execute Reference state = state.mapClassical (fun entry =>
      ((loaderStep N entry.1).1, (entry.2, (loaderStep N entry.1).2))) := by
  refine (ConstantWord.constantWord_fold_execute (Layout.modulusCell ctx (modulusBits N))
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) Reference state).trans ?_
  congr 1

/-- Store and actual nested path after loading and scanning the original sixteen proposals. -/
def step (N : Nat) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (store : Store (Layout.context ctx (modulusBits N))) :
    Store (Layout.context ctx (modulusBits N)) × (circuit N sample).Path :=
  let loaded := loaderStep N store
  let selected := Proposal.foldSteps (Layout.underRead sample (modulusBits N))
    (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
    (List.ofFn (fun proposal : Fin residueProposalCount => proposal)) loaded.1
  (selected.1, (loaded.2, selected.2))

/-- The real two-stage program follows its exact joint store/path update on every matrix block. -/
theorem samplerScan_execute (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N))) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Layout.context ctx (modulusBits N)) Reference History) :
    (circuit N sample).execute Reference state = state.mapClassical (fun entry =>
      ((step N sample entry.1).1, (entry.2, (step N sample entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (loader ctx N) _ (loaderStep N)
    (Proposal.foldSteps (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
      (List.ofFn (fun proposal : Fin residueProposalCount => proposal)))
    (loader_execute N)
    (Proposal.proposalFold_execute (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))
      (List.ofFn (fun proposal : Fin residueProposalCount => proposal))) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Scan
