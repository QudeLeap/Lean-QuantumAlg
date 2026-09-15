/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Output.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Complete output and reusable-bank state of the actual native batch

Each real output block retains the exact reloaded local basis state, multiplied
by that output's original source probability and the incoming reference block.
The formula includes every local and external matrix coordinate, so the same
bank is proved ready for reuse without hiding its remaining quantum state.
There is no input-state initialization or independence premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU
open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The original source seed on the single actual bank retained after all sixteen rounds. -/
def restoredSeed : (context base noQuantum N).register.Index :=
  (RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (nativeBatch_context_wires base noQuantum N)).symm
      (ShortDLP.CompiledMAU.reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)

/-- Every complete output-reference matrix block has the actual bank seed and source probability. -/
theorem nativeBatch_output_joint_entry (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (selected : (resultShape N).Value)
    (left right : (context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code base noQuantum N).execute Reference state).mapClassical
        (fun entry => (run base noQuantum N).output.eval entry.1)).block selected).matrix
          (left, leftRef) (right, rightRef) =
      if left = restoredSeed base noQuantum N ∧ right = restoredSeed base noQuantum N then
        ExecutionState.referenceFiberSum state
          (fun _ _ => ((sourceDistribution input selected).toReal : ℂ)) leftRef rightRef
      else 0 := by
  have seeded : BasisSeeded.Holds (restoredSeed base noQuantum N)
      ((code base noQuantum N).execute Reference state) :=
    nativeBatch_complete_seedBlocks base noQuantum N state
  have observed := BasisSeeded.readout_entry (restoredSeed base noQuantum N)
    ((code base noQuantum N).execute Reference state) seeded
    (fun store => (run base noQuantum N).output.eval store) selected left right leftRef rightRef
  exact observed.trans
    (congrArg (fun coefficient : ℂ =>
      if left = restoredSeed base noQuantum N ∧ right = restoredSeed base noQuantum N
        then coefficient else 0)
      (nativeBatch_output_indicator_reference base noQuantum input state selected leftRef rightRef))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
