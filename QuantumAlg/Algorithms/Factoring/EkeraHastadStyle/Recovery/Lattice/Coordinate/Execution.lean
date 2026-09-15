/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Coordinate

/-!
# Full actual execution of native lattice coordinate arithmetic

The same actual multiplication and subtraction update each original
store-keyed quantum-reference block. The one lexical product word is
supplied by its actual scope and removed by the matching release. The final
history contains the two genuine instruction paths, with arbitrary incoming
classical correlations and external reference systems retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual multiplication followed by subtraction acts on the full original classical blocks. -/
theorem nativeLattice_coordinate_body_execute
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx width) Reference History) :
    (body coefficient source target).execute Reference state = state.mapClassical (fun entry =>
      (bodyStore coefficient source target entry.1, (entry.2, ((), ())))) := by
  simp only [body, Circuit.execute_seq, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  dsimp only [bodyStore]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx width) × History)
    (D := Store (context ctx width) × (History × (body coefficient source target).Path))
    (R := Register.prod (context ctx width).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (context ctx width) × History)
    (D := Store (context ctx width) × (History × (body coefficient source target).Path))
    (R := Register.prod (context ctx width).register Reference) _ state _).symm

/-- Complete actual coordinate execution returns the same store and two recorded instruction paths.
-/
theorem nativeLattice_coordinate_execute
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code coefficient source target).execute Reference state = state.mapClassical (fun entry =>
      (storeStep coefficient source target entry.1, (entry.2, ((), ())))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (body coefficient source target)
    (fun store => (bodyStore coefficient source target store, ((), ())))
    (fun reference {history} _ current => by
      refine (nativeLattice_coordinate_body_execute
        coefficient source target reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh) × history)
        (D := Store (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh) × (history × (body coefficient source target).Path))
        (R := Register.prod (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh).register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh) × history)
        (D := Store (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh) × (history × (body coefficient source target).Path))
        (R := Register.prod (ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh).register reference) _ current _).symm)
    Reference state).trans ?_
  dsimp only [storeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code coefficient source target).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × (code coefficient source target).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate
