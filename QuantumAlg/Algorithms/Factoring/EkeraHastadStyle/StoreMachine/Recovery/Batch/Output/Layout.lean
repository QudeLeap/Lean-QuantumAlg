/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Shape
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Layout

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput

open Execution
open ClassicalRoutines

noncomputable section

/-- Public optional factor shape produced by the fixed-batch recovery tail. -/
public abbrev OutputShape (N : Nat) : CShape := .option (.unsignedWord (modulusBits N))

/-- Shaped optional value obtained by truncating one selected natural number. -/
def outputValue {N : Nat} : Option Nat → CShape.Value (OutputShape N)
  | none => .optionNone
  | some factor => .optionSome (CShape.wordOfNat (modulusBits N) factor)

/-- Persistent wide selection, one narrow scratch word, and the endpoint cell. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  selection : FirstAccepted.Refs ctx
    (QuadraticCandidateCheck.CandidateWidth (LatticePairCandidateRecovery.Width N))
  narrow : CWriteRef ctx (.unsignedWord (modulusBits N))
  result : CWriteRef ctx (OutputShape N)

/-- The acceptance latch survives the preceding word resize. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  acceptedAvoidsNarrow : refs.narrow.key ∉
    (FirstAccepted.cellRead refs.selection.accepted).storageKeys

/-- Every write avoided by one arbitrary structural caller read. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  narrow : refs.narrow.key ∉ other.storageKeys
  result : refs.result.key ∉ other.storageKeys

/-- Exact shaped result and complete structural caller frame of the actual two operations. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) (before after : Store ctx) : Prop where
  output : after.read (FirstAccepted.cellRead refs.result) =
    outputValue (QuadraticCandidateSelect.selectedOption refs.selection before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput
