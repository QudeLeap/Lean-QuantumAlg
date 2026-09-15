/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Initialization

/-!
# Full joint execution of the actual initial basis loading

The original first-row sequence and both actual power-of-two loops compose
through their proved interpreter equations. The result is the same recorded
store used by the source-value proofs, with all three real loading paths.
Every incoming Store-history block and the complete quantum-reference matrix
are retained, including arbitrary classical and quantum correlations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem power_pair_execute {width : Nat} (count : Nat)
    (left right : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (PowerOfTwo.code count left) (PowerOfTwo.code count right)).execute
      Reference state = state.mapClassical (fun entry =>
        (PowerOfTwo.storeStep count right (PowerOfTwo.storeStep count left entry.1),
          (entry.2, (((), fun _ : Fin count => ()), ((), fun _ : Fin count => ()))))) := by
  refine (Circuit.execute_seq_mapClassical
    (PowerOfTwo.code count left) (PowerOfTwo.code count right)
    (fun current => (PowerOfTwo.storeStep count left current, ((), fun _ : Fin count => ())))
    (fun current => (PowerOfTwo.storeStep count right current, ((), fun _ : Fin count => ())))
    (fun reference {history} _ current => by
      refine (PowerOfTwo.nativeLattice_powerOfTwo_execute count left reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history)
        (D := Store ctx × (history × (Unit × (Fin count → Unit))))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history)
        (D := Store ctx × (history × (Unit × (Fin count → Unit))))
        (R := Register.prod ctx.register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (PowerOfTwo.nativeLattice_powerOfTwo_execute count right reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history)
        (D := Store ctx × (history × (Unit × (Fin count → Unit))))
        (R := Register.prod ctx.register reference) _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history)
        (D := Store ctx × (history × (Unit × (Fin count → Unit))))
        (R := Register.prod ctx.register reference) _ current _).symm)
    Reference state).trans ?_
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × ((Unit × (Fin count → Unit)) × (Unit × (Fin count → Unit)))))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History)
    (D := Store ctx × (History × ((Unit × (Fin count → Unit)) × (Unit × (Fin count → Unit)))))
    (R := Register.prod ctx.register Reference) _ state _).symm

/-- The exact actual basis-loading state has the same store as the source-value contract. -/
theorem nativeLattice_basis_initialization_execute {sourceWidth : Nat}
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (BasisLayout.context ctx width) Reference History) :
    (code first second width count).execute Reference state = state.mapClassical (fun entry =>
      (storeStep first second width count entry.1,
        (entry.2, (((), ((), ())),
          (((), fun _ : Fin count => ()), ((), fun _ : Fin count => ())))))) := by
  refine (Circuit.execute_seq_mapClassical (firstCode first second width)
    (.seq (secondCode ctx width count) (thirdCode ctx width count))
    (fun current => (FirstRow.storeStep (BasisLayout.underRead first width)
      (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width) current,
      ((), ((), ()))))
    (fun current => (PowerOfTwo.storeStep count (BasisLayout.thirdRow ctx width).second
      (PowerOfTwo.storeStep count (BasisLayout.secondRow ctx width).first current),
      (((), fun _ : Fin count => ()), ((), fun _ : Fin count => ()))))
    (fun reference {history} _ current => by
      refine (FirstRow.nativeLattice_firstRow_execute (BasisLayout.underRead first width)
        (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width)
        reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (BasisLayout.context ctx width) × history)
        (D := Store (BasisLayout.context ctx width) × (history × (Unit × (Unit × Unit))))
        (R := Register.prod (BasisLayout.context ctx width).register reference)
        _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (BasisLayout.context ctx width) × history)
        (D := Store (BasisLayout.context ctx width) × (history × (Unit × (Unit × Unit))))
        (R := Register.prod (BasisLayout.context ctx width).register reference) _ current _).symm)
    (fun reference {history} _ current => by
      refine (power_pair_execute count (BasisLayout.secondRow ctx width).first
        (BasisLayout.thirdRow ctx width).second reference current).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store (BasisLayout.context ctx width) × history)
        (D := Store (BasisLayout.context ctx width) ×
          (history × ((Unit × (Fin count → Unit)) × (Unit × (Fin count → Unit)))))
        (R := Register.prod (BasisLayout.context ctx width).register reference)
        _ current _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store (BasisLayout.context ctx width) × history)
        (D := Store (BasisLayout.context ctx width) ×
          (history × ((Unit × (Fin count → Unit)) × (Unit × (Fin count → Unit)))))
        (R := Register.prod (BasisLayout.context ctx width).register reference) _ current _).symm)
    Reference state).trans ?_
  dsimp only [storeStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (BasisLayout.context ctx width) × History)
    (D := Store (BasisLayout.context ctx width) × (History × (code first second width count).Path))
    (R := Register.prod (BasisLayout.context ctx width).register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (BasisLayout.context ctx width) × History)
    (D := Store (BasisLayout.context ctx width) × (History × (code first second width count).Path))
    (R := Register.prod (BasisLayout.context ctx width).register Reference) _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization
