/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Semantics

/-!
# Actual internal allocation of the complete-addition classifier

The actual workspace instruction supplies both distinct cell identities and
the original initialized zero word. A continuation receives the original
complete branch predicates without any caller initialization premise.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem classifierOfCells_keys (cells : Cells ctx (classifierShapes width)) :
    (classifierOfCells cells).keys = cells.keys := by
  cases cells with
  | cons left rest =>
    cases rest with
    | cons right rest =>
      cases rest with
      | cons x rest =>
        cases rest with
        | cons y rest =>
          cases rest with
          | cons zero rest =>
            cases rest with
            | cons yZero rest =>
              cases rest
              rfl

/-- Actual allocation establishes every separation used by the internal classifier proof. -/
theorem classifierOfCells_separation {outer : RuntimeCtx kind}
    (left right : CInputRef outer (PointShape width))
    (cells : Cells ctx (classifierShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (classifierOfCells cells).Separation (transport.liftInput left)
      (transport.liftInput right) := by
  constructor
  · rw [classifierOfCells_keys]
    exact Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [classifierOfCells_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      member left
  · intro key member
    rw [classifierOfCells_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      member right

/-- The original zero word is supplied by real lexical initialization, including width zero. -/
theorem classifierOfCells_zero_initialized (cells : Cells ctx (classifierShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    store.read (classifierRead (classifierOfCells cells).zero) = .unsignedWord 0 := by
  cases cells with
  | cons left rest =>
    cases rest with
    | cons right rest =>
      cases rest with
      | cons x rest =>
        cases rest with
        | cons y rest =>
          cases rest with
          | cons zero rest =>
            cases rest with
            | cons yZero rest =>
              cases rest
              exact initialized.2.2.2.2.1

private theorem classifierStore_readsAs {outer : RuntimeCtx kind}
    (left right : CInputRef outer (PointShape width))
    (cells : Cells ctx (classifierShapes width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (source : Store outer) (before : Store ctx)
    (reads : transport.ReadsAs source before) :
    transport.ReadsAs source
      (classifierStore (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells) before) := by
  intro shape input
  refine (classifierStore_preserves _ _ _ _ (transport.liftInput input) ?_).trans (reads input)
  intro key member
  rw [classifierOfCells_keys] at member
  exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated member input

/-- Real allocation and classification discharge the continuation's original input predicates. -/
theorem withClassification_actualRecord_post (left right : CInputRef ctx (PointShape width))
    (body : ∀ {inner : RuntimeCtx kind}, Classifier inner width →
      Transport ctx inner → Circuit inner inner)
    (Post : Store ctx → Store ctx → Prop)
    (bodyContract : ∀ {inner : RuntimeCtx kind} (classifier : Classifier inner width)
      (transport : Transport ctx inner),
      ∃ step : Store inner → Store inner × (body classifier transport).Path,
        (∀ (Reference : Register) {History : Type} [Fintype History]
          (state : State inner Reference History),
          (body classifier transport).execute Reference state = state.mapClassical (fun entry =>
            ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
        ∀ (source : Store ctx) (before : Store inner), transport.ReadsAs source before →
          classifier.Ready before (source.read left) (source.read right) →
            ∃ target : Store ctx, Post source target ∧ transport.ReadsAs target (step before).1) :
    ∃ step : Store ctx → Store ctx × (withClassification left right body).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withClassification left right body).execute Reference state = state.mapClassical
          (fun entry => ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, Post before (step before).1 := by
  apply withCells_actualRecord_initialized_post ctx (classifierShapes width)
    (fun cells _ transport _ =>
      .seq (classifierBody (transport.liftInput left) (transport.liftInput right)
        (classifierOfCells cells)) (body (classifierOfCells cells) transport)) Post
  intro inner cells distinct transport separated
  obtain ⟨bodyStep, bodyEquation, bodyCorrect⟩ := bodyContract (classifierOfCells cells) transport
  refine ⟨Circuit.sequenceRecord _ _ (classifierRecord _ _ _) bodyStep,
    Circuit.execute_sequenceRecord _ _ _ _ (classifierBody_execute _ _ _) bodyEquation, ?_⟩
  intro source before reads initialized
  have ready := classifierBody_ready (transport.liftInput left) (transport.liftInput right)
    (classifierOfCells cells) (classifierOfCells_separation left right cells distinct
      transport separated) before (classifierOfCells_zero_initialized cells before initialized)
  rw [reads left, reads right] at ready
  obtain ⟨target, post, returned⟩ := bodyCorrect source
    (classifierStore (transport.liftInput left) (transport.liftInput right)
      (classifierOfCells cells) before)
    (classifierStore_readsAs left right cells transport separated source before reads) ready
  refine ⟨target, post, ?_⟩
  rw [Circuit.sequenceRecord_store, classifierRecord_store]
  exact returned

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
