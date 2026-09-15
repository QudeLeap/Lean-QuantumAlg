/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Target.Scale

/-!
# Full actual execution of a source target preimage

The real resize and shared left-shift loop act on the complete incoming
Store-history and quantum-reference state. Their recorded path retains the
actual loop index function. The complete borrowed interface is restored by
the same real classical instructions, with arbitrary incoming correlations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetScale

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The full actual state follows the same recorded resize and finite shift updates. -/
theorem nativeLattice_targetScale_execute
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code input output count).execute Reference state = state.mapClassical (fun entry =>
      (storeStep input output count entry.1, (entry.2, ((), fun _ : Fin count => ())))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (FirstRow.resizeOp input output))
    (PowerOfTwo.shifts count output)
    (fun current => (current.applyOp (FirstRow.resizeOp input output), ()))
    (fun current => (PowerOfTwo.shiftsStore count output current, fun _ : Fin count => ()))
    (fun reference {history} _ current => by
      refine (Circuit.execute_classical_mapClassical
        (FirstRow.resizeOp input output) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × Unit))
        (R := Register.prod ctx.register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (PowerOfTwo.shifts_execute count output reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (Fin count → Unit)))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (Fin count → Unit)))
        (R := Register.prod ctx.register reference) _ current _).symm)
    Reference state).trans ?_
  dsimp only [storeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code input output count).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code input output count).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

/-- Actual preimage loading restores every borrowed classical and quantum reference block. -/
theorem nativeLattice_targetScale_borrowedRestored
    (input : CInputRef ctx (.unsignedWord sourceWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (count : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code input output count).BorrowedRestored Reference state
      ((code input output count).execute Reference state) :=
  Circuit.borrowedRestored_seq (.classical (FirstRow.resizeOp input output))
    (PowerOfTwo.shifts count output) state
    (Circuit.borrowedRestored_classical (FirstRow.resizeOp input output) state)
    (Circuit.borrowedRestored_iterate (.classical (PowerOfTwo.shiftOp output)) Reference
      (fun {_} _ current =>
        Circuit.borrowedRestored_classical (PowerOfTwo.shiftOp output) current) count _)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetScale
