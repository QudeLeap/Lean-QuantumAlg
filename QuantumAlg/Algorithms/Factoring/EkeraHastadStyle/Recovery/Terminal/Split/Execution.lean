/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Complete execution of the actual terminal sample split

The same terminal decoder, two resizing instructions and finite shift loop
act on every incoming store block. Composition retains their real paths and
all correlations with the original quantum bank and external reference.
The one lexical full-index word is supplied and released by the existing
workspace constructor.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

private theorem shift_high_execute
    (refs : Refs ctx m ell) (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx m ell) Reference History) :
    (Circuit.seq (TerminalShift.code ell (full ctx m ell))
      (.classical (highOp refs))).execute Reference state = state.mapClassical (fun entry =>
        ((TerminalShift.storeStep ell (full ctx m ell) entry.1).applyOp (highOp refs),
          (entry.2, ((fun _ : Fin ell => ()), ())))) := by
  refine (Circuit.execute_seq_mapClassical
    (TerminalShift.code ell (full ctx m ell)) (.classical (highOp refs))
    (fun current => (TerminalShift.storeStep ell (full ctx m ell) current,
      fun _ : Fin ell => ()))
    (fun current => (current.applyOp (highOp refs), ()))
    (fun reference {history} _ current => by
      refine (TerminalShift.nativeRecovery_terminal_shifts_execute
        ell (full ctx m ell) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × (Fin ell → Unit)))
        (R := Register.prod (context ctx m ell).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × (Fin ell → Unit)))
        (R := Register.prod (context ctx m ell).register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (Circuit.execute_classical_mapClassical (highOp refs) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × Unit))
        (R := Register.prod (context ctx m ell).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × Unit))
        (R := Register.prod (context ctx m ell).register reference) _ current _).symm)
    Reference state).trans ?_
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × ((Fin ell → Unit) × Unit)))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × ((Fin ell → Unit) × Unit)))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).symm

private theorem extraction_execute
    (refs : Refs ctx m ell) (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx m ell) Reference History) :
    (Circuit.seq (.classical (lowOp refs))
      (.seq (TerminalShift.code ell (full ctx m ell)) (.classical (highOp refs)))).execute
        Reference state = state.mapClassical (fun entry =>
          ((TerminalShift.storeStep ell (full ctx m ell)
              (entry.1.applyOp (lowOp refs))).applyOp (highOp refs),
            (entry.2, ((), ((fun _ : Fin ell => ()), ()))))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (lowOp refs))
    (.seq (TerminalShift.code ell (full ctx m ell)) (.classical (highOp refs)))
    (fun current => (current.applyOp (lowOp refs), ()))
    (fun current => ((TerminalShift.storeStep ell (full ctx m ell) current).applyOp
      (highOp refs), ((fun _ : Fin ell => ()), ())))
    (fun reference {history} _ current => by
      refine (Circuit.execute_classical_mapClassical (lowOp refs) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × Unit))
        (R := Register.prod (context ctx m ell).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × Unit))
        (R := Register.prod (context ctx m ell).register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (shift_high_execute refs reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × ((Fin ell → Unit) × Unit)))
        (R := Register.prod (context ctx m ell).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × ((Fin ell → Unit) × Unit)))
        (R := Register.prod (context ctx m ell).register reference) _ current _).symm)
    Reference state).trans ?_
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × (Unit × ((Fin ell → Unit) × Unit))))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × (Unit × ((Fin ell → Unit) × Unit))))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).symm

/-- The real decoder and extraction body has exactly its recorded full-state update. -/
theorem nativeRecovery_terminal_split_body_execute
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx m ell) Reference History) :
    (body input refs).execute Reference state = state.mapClassical (fun entry =>
      ((bodyStep input refs entry.1).1, (entry.2, (bodyStep input refs entry.1).2))) := by
  -- Compose each suffix at its original finite path carrier. This keeps the
  -- shift's function-path representation out of intermediate state matching.
  refine (Circuit.execute_seq_mapClassical
    (terminalCircuit (underRead input m ell) (full ctx m ell))
    (.seq (.classical (lowOp refs))
      (.seq (TerminalShift.code ell (full ctx m ell)) (.classical (highOp refs))))
    (terminalStep (underRead input m ell) (full ctx m ell))
    (fun current => ((TerminalShift.storeStep ell (full ctx m ell)
      (current.applyOp (lowOp refs))).applyOp (highOp refs),
      ((), ((fun _ : Fin ell => ()), ()))))
    (fun reference {history} _ current => by
      refine (nativeRecovery_terminal_execute (underRead input m ell)
        (full ctx m ell) reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history ×
          (terminalCircuit (underRead input m ell) (full ctx m ell)).Path))
        (R := Register.prod (context ctx m ell).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history ×
          (terminalCircuit (underRead input m ell) (full ctx m ell)).Path))
        (R := Register.prod (context ctx m ell).register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (extraction_execute refs reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × (Unit × ((Fin ell → Unit) × Unit))))
        (R := Register.prod (context ctx m ell).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (context ctx m ell) × history)
        (D := Store (context ctx m ell) × (history × (Unit × ((Fin ell → Unit) × Unit))))
        (R := Register.prod (context ctx m ell).register reference) _ current _).symm)
    Reference state).trans ?_
  dsimp only [bodyStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × (body input refs).Path))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx m ell) × History)
    (D := Store (context ctx m ell) × (History × (body input refs).Path))
    (R := Register.prod (context ctx m ell).register Reference) _ state _).symm

/-- Actual lexical allocation and release preserve the complete recorded execution equation. -/
theorem nativeRecovery_terminal_split_execute
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code input refs).execute Reference state = state.mapClassical (fun entry =>
      ((step input refs entry.1).1, (entry.2, (step input refs entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh
    (body input refs) (bodyStep input refs)
    (fun reference {history} _ current => by
      refine (nativeRecovery_terminal_split_body_execute input refs reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (ctx.addWorkspace ctx.canonicalFreshKey
          (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh) × history)
        (D := Store (ctx.addWorkspace ctx.canonicalFreshKey
          (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh) ×
          (history × (body input refs).Path))
        (R := Register.prod (ctx.addWorkspace ctx.canonicalFreshKey
          (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh).register reference)
        _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (ctx.addWorkspace ctx.canonicalFreshKey
          (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh) × history)
        (D := Store (ctx.addWorkspace ctx.canonicalFreshKey
          (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh) ×
          (history × (body input refs).Path))
        (R := Register.prod (ctx.addWorkspace ctx.canonicalFreshKey
          (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh).register reference)
        _ current _).symm)
    Reference state).trans ?_
  dsimp only [step]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code input refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code input refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit
