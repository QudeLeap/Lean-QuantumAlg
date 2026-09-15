/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Target.Centering

/-!
# Full execution of the actual centered-coordinate branches

The actual four-instruction prefix and two stored decisions determine one
complete recorded update. Each branch theorem applies the existing native
interpreter equation to the real chosen circuit. All Store-history and
quantum-reference blocks are retained, without an initialization, separation,
or absence-of-borrowed-quantum premise on the incoming state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- All four actual preparation instructions retain their chronological paths and full blocks. -/
theorem nativeLattice_targetCentering_decision_execute (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (decisionCode refs).execute Reference state = state.mapClassical (fun entry =>
      (decisionStore refs entry.1, (entry.2, ((), ((), ((), ())))))) := by
  simp only [decisionCode, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  dsimp only [decisionStore]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (decisionCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (decisionCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

/-- The actual negative arm performs complement and increment on every complete input block. -/
theorem nativeLattice_targetCentering_negate_execute (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (negateCode refs).execute Reference state = state.mapClassical (fun entry =>
      (negateStore refs entry.1, (entry.2, ((), ())))) := by
  simp only [negateCode, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  dsimp only [negateStore]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (negateCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (negateCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

private theorem below_execute (refs : Refs ctx width) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (belowChoice refs value).execute Reference state = state.mapClassical (fun entry =>
      ((belowStep refs value entry.1).1, (entry.2, (belowStep refs value entry.1).2))) := by
  unfold belowChoice
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, belowStep]
        refine (Circuit.execute_classical_mapClassical (subtractOp refs) Reference state).trans ?_
        refine (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × Unit))
          (R := Register.prod ctx.register Reference) _ state _).trans ?_
        exact (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × Unit))
          (R := Register.prod ctx.register Reference) _ state _).symm
      · simp only [CShape.Value.toBool, belowStep]
        refine (nativeLattice_targetCentering_negate_execute refs Reference state).trans ?_
        refine (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × (negateCode refs).Path))
          (R := Register.prod ctx.register Reference) _ state _).trans ?_
        exact (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × (negateCode refs).Path))
          (R := Register.prod ctx.register Reference) _ state _).symm

/-- The actual inner stored branch records its selected value and complete arithmetic path. -/
theorem nativeLattice_targetCentering_nonzero_execute (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (nonzeroCode refs).execute Reference state = state.mapClassical (fun entry =>
      ((nonzeroStep refs entry.1).1, (entry.2, (nonzeroStep refs entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (.storage refs.belowHalf.toCStorageRef)
    (belowChoice refs) (belowStep refs) (below_execute refs) Reference state).trans ?_
  dsimp only [nonzeroStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (nonzeroCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (nonzeroCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

private theorem zero_execute (refs : Refs ctx width) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (zeroChoice refs value).execute Reference state = state.mapClassical (fun entry =>
      ((zeroStep refs value entry.1).1, (entry.2, (zeroStep refs value entry.1).2))) := by
  unfold zeroChoice
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, zeroStep]
        refine (nativeLattice_targetCentering_nonzero_execute refs Reference state).trans ?_
        refine (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × (nonzeroCode refs).Path))
          (R := Register.prod ctx.register Reference) _ state _).trans ?_
        exact (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × (nonzeroCode refs).Path))
          (R := Register.prod ctx.register Reference) _ state _).symm
      · simp only [CShape.Value.toBool, zeroStep]
        refine (Circuit.execute_classical_mapClassical (zeroOp refs) Reference state).trans ?_
        refine (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × Unit))
          (R := Register.prod ctx.register Reference) _ state _).trans ?_
        exact (Circuit.mapClassical_canonicalDecision
          (C := Store ctx × History) (D := Store ctx × (History × Unit))
          (R := Register.prod ctx.register Reference) _ state _).symm

/-- The outer stored equality dispatches each actual input fiber to its original chosen arm. -/
theorem nativeLattice_targetCentering_selection_execute (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (selectionCode refs).execute Reference state = state.mapClassical (fun entry =>
      ((selectionStep refs entry.1).1, (entry.2, (selectionStep refs entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (.storage refs.isZero.toCStorageRef)
    (zeroChoice refs) (zeroStep refs) (zero_execute refs) Reference state).trans ?_
  dsimp only [selectionStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (selectionCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (selectionCode refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

/-- The full real centered-coordinate computation follows its actual decision and branch record. -/
theorem nativeLattice_targetCentering_execute (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (decisionCode refs) (selectionCode refs)
    (fun store => (decisionStore refs store, ((), ((), ((), ()))))) (selectionStep refs)
    (fun reference {history} _ initial => by
      refine (nativeLattice_targetCentering_decision_execute refs reference initial).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (decisionCode refs).Path))
        (R := Register.prod ctx.register reference) _ initial _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (decisionCode refs).Path))
        (R := Register.prod ctx.register reference) _ initial _).symm)
    (fun reference {history} _ initial => by
      refine (nativeLattice_targetCentering_selection_execute refs reference initial).trans ?_
      refine (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (selectionCode refs).Path))
        (R := Register.prod ctx.register reference) _ initial _).trans ?_
      exact (Circuit.mapClassical_canonicalDecision
        (C := Store ctx × history) (D := Store ctx × (history × (selectionCode refs).Path))
        (R := Register.prod ctx.register reference) _ initial _).symm)
    Reference state).trans ?_
  dsimp only [step]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store ctx × History) (D := Store ctx × (History × (code refs).Path))
    (R := Register.prod ctx.register Reference) _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering
