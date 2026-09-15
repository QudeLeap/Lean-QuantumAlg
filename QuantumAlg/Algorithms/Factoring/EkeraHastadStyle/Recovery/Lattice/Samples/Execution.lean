/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Samples.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split.Execution
import Mathlib.Data.Fintype.Prod

/-!
# Full-state execution of the original ordered pair decoder

The actual first decoder returns before the actual second decoder starts.
Their composed update records both real paths and preserves every incoming
store-keyed quantum-reference block. This is the execution prefix supplying
the four concrete source fields to the subsequent lattice computation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- The same actual ordered decoder has exactly its recorded complete joint-state update. -/
theorem nativeLattice_sample_decode_execute
    (first second : CInputRef ctx (.bits ((ell + m) + ell))) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx m ell) Reference History) :
    (decode first second).execute Reference state = state.mapClassical (fun entry =>
      ((decodeStep first second entry.1).1, (entry.2, (decodeStep first second entry.1).2))) := by
  let : Fintype (History ×
      (TerminalSplit.code (underRead first m ell) (firstRefs ctx m ell)).Path) :=
    @instFintypeProd _ _ inferInstance (Circuit.pathFintype _)
  simp only [decode, Circuit.execute_seq, TerminalSplit.nativeRecovery_terminal_split_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  dsimp only [decodeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × (decode first second).Path))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × (decode first second).Path))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.SampleLayout
