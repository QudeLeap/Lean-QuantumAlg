/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Indexed.Values

/-!
# Complete structural read preservation through actual small-base records

Each original doubling writes the same two coordinate arrays and four
scalar cells. Every caller read outside those actual outputs survives all
sixteen doublings and every next-base iteration, including reads used as
the second point's original input.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- A proof property of the six actual output identities of the existing coordinate frame. -/
def OutputFree (frame : CoordinateFrame ctx width length) {shape : CShape}
    (input : CInputRef ctx shape) : Prop :=
  ∀ key ∈ [frame.x.key, frame.y.key, frame.work.product.key, frame.work.inverse.key,
    frame.work.temporary.key, frame.work.slope.key], key ∉ input.storageKeys

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} (frame : CoordinateFrame ctx width length)
  (spec : ModulusSpec width) (environment : model.Environment)
  {shape : CShape} (observed : CInputRef ctx shape) (free : OutputFree frame observed)

include free

private lemma double_read (source destination : Fin length)
    (before : Store ctx × model.HiddenState) :
    (frame.doubleRecord spec source destination environment before).1.1.read observed =
      before.1.read observed := by
  rw [frame.doubleRecord_store]
  exact frame.doubleStore_read_other spec source destination before.1 observed
    (free _ (by simp)) (free _ (by simp)) (free _ (by simp))
    (free _ (by simp)) (free _ (by simp)) (free _ (by simp))

private lemma repeated_read (row : Fin length) (count : Nat)
    (before : Store ctx × model.HiddenState) :
    (frame.repeatedDoubleRecord spec row count environment before).1.1.read observed =
      before.1.read observed := by
  exact Circuit.forRangeRecord_invariant count (fun _ => frame.doubleCircuit spec row row)
    (fun _ => frame.doubleRecord spec row row environment)
    (fun _ current => current.1.read observed = before.1.read observed)
    (fun _ current established =>
      (double_read frame spec environment observed free row row current).trans established)
    before rfl

attribute [local irreducible] CoordinateFrame.doubleRecord

private lemma baseStep_read (source destination : Fin length)
    (before : Store ctx × model.HiddenState) :
    (frame.baseStepRecord spec source destination environment before).1.1.read observed =
      before.1.read observed := by
  rw [frame.baseStepRecord_state, frame.successiveRecord_state]
  exact (repeated_read frame spec environment observed free destination 15
    (frame.doubleRecord spec source destination environment before).1).trans
      (double_read frame spec environment observed free source destination before)

/-- All actual next-base calls preserve every original structural read outside the six outputs. -/
lemma bases_read {baseCount : Nat}
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) (before : Store ctx × model.HiddenState) :
    (frame.prepareBasesAtRecord spec sourceX sourceY rows environment before).1.1.read observed =
      before.1.read observed := by
  let zero : Fin (baseCount + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let initial := frame.seedRecord (model := model) sourceX sourceY (rows zero) before
  have seeded := frame.seedRecord_read_other sourceX sourceY (rows zero) before observed
    (free _ (by simp)) (free _ (by simp))
  exact Circuit.forRangeRecord_invariant baseCount
    (fun index => frame.baseStep spec (rows index.castSucc) (rows index.succ))
    (fun index => frame.baseStepRecord spec (rows index.castSucc) (rows index.succ) environment)
    (fun _ current => current.1.read observed = before.1.read observed)
    (fun index current established =>
      (baseStep_read frame spec environment observed free (rows index.castSucc) (rows index.succ)
        current).trans established) initial.1 seeded

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer.Preparation
