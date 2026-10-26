/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Record
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Order
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Constants
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Preservation
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Actual successive in-place doublings of one original small-base point

The existing finite-range record feeds each actual returned Store into
the next original doubling. The loaded constants and original prime order
are maintained throughout, with no assumption that a power-of-two scalar
is below that order. All other coordinate rows retain their original words.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : CoordinateFrame ctx width length)

/-- The same actual finite-range record used by successive original in-place doubling calls. -/
def repeatedDoubleRecord (spec : ModulusSpec width) (row : Fin length) (count : Nat)
    (environment : model.Environment) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (Circuit.forRange count (fun _ => frame.doubleCircuit (model := model) spec row row)).Path :=
  Circuit.forRangeRecord count (fun _ => frame.doubleCircuit spec row row)
    (fun _ => frame.doubleRecord spec row row environment)

attribute [local irreducible] doubleRecord

/-- Actual in-place doublings preserve the original constants and give their exact group values. -/
lemma repeatedDoubleRecord_values (curve : CurveSpec width) (row : Fin length) (count : Nat)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (before.1.read (rowRead frame.x row))
      (before.1.read (rowRead frame.y row)) point) :
    let returned := (frame.repeatedDoubleRecord curve.field row count environment before).1.1
    returned.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      returned.read frame.curveA = before.1.read frame.curveA ∧
      CoordinateValue curve (returned.read (rowRead frame.x row))
        (returned.read (rowRead frame.y row)) ((2 ^ count) • point) := by
  apply Circuit.forRangeRecord_invariant count
    (fun _ => frame.doubleCircuit curve.field row row)
    (fun _ => frame.doubleRecord curve.field row row environment)
    (fun processed current =>
      current.1.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
        current.1.read frame.curveA = before.1.read frame.curveA ∧
        CoordinateValue curve (current.1.read (rowRead frame.x row))
          (current.1.read (rowRead frame.y row)) ((2 ^ processed) • point))
  · intro index current established
    refine ⟨(frame.doubleRecord_read_modulus curve.field row row environment current).trans
      established.1, (frame.doubleRecord_read_curveA curve.field row row environment current).trans
        established.2.1, ?_⟩
    have actual := frame.doubleRecord_coordinateValue curve row row environment current
      ((2 ^ index.val) • point) (established.1.trans loaded)
      (by rw [established.2.1]; exact curveValue) established.2.2
      (pow_two_nsmul_double_ne_zero point order index.val prime large original)
    have scalar : (2 ^ index.val) • point + (2 ^ index.val) • point =
        (2 ^ (index.val + 1)) • point := by
      rw [pow_succ, Nat.mul_two, add_nsmul]
    rw [scalar] at actual
    exact actual
  · exact ⟨rfl, rfl, by simpa only [pow_zero, one_nsmul] using input⟩

/-- Every true in-place call preserves every unvisited original coordinate row. -/
lemma repeatedDoubleRecord_read_other_row (spec : ModulusSpec width)
    (selected : Fin length) (count : Nat) (environment : model.Environment)
    (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.repeatedDoubleRecord spec selected count environment before).1.1.read
      (rowRead array row) = before.1.read (rowRead array row) := by
  exact Circuit.forRangeRecord_invariant count (fun _ => frame.doubleCircuit spec selected selected)
    (fun _ => frame.doubleRecord spec selected selected environment)
    (fun _ current => current.1.read (rowRead array row) = before.1.read (rowRead array row))
    (fun _ current established =>
      (frame.doubleRecord_read_other_row spec selected selected environment current array row
        different).trans established) before rfl

private lemma pow_two_nsmul_double {G : Type*} [AddGroup G] (point : G) (count : Nat) :
    (2 ^ count) • (point + point) = (2 ^ (count + 1)) • point := by
  rw [← two_nsmul, ← mul_nsmul, ← pow_succ']

/-- Actual first doubling followed by an arbitrary number of true in-place doublings. -/
def successiveRecord (spec : ModulusSpec width) (source destination : Fin length) (extra : Nat)
    (environment : model.Environment) :=
  Circuit.sequenceRecord (frame.doubleCircuit (model := model) spec source destination)
    (Circuit.forRange extra (fun _ => frame.doubleCircuit spec destination destination))
    (frame.doubleRecord spec source destination environment)
    (frame.repeatedDoubleRecord spec destination extra environment)

/-- The arbitrary-count actual record returns its actual final in-place-doubling state. -/
lemma successiveRecord_state (spec : ModulusSpec width) (source destination : Fin length)
    (extra : Nat) (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.successiveRecord spec source destination extra environment before).1 =
      (frame.repeatedDoubleRecord spec destination extra environment
        (frame.doubleRecord spec source destination environment before).1).1 := rfl

/-- Specializing only the number of calls gives the original sixteen-doubling returned state. -/
lemma baseStepRecord_state (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState) :
    (frame.baseStepRecord spec source destination environment before).1 =
      (frame.successiveRecord spec source destination 15 environment before).1 := rfl

attribute [local irreducible] baseStepRecord successiveRecord repeatedDoubleRecord

/-- Arbitrary-count actual successive doublings give their exact original group value. -/
lemma successiveRecord_values (curve : CurveSpec width) (source destination : Fin length)
    (extra : Nat) (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (before.1.read (rowRead frame.x source))
      (before.1.read (rowRead frame.y source)) point) :
    let returned := (frame.successiveRecord curve.field source destination extra environment
      before).1.1
    returned.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      returned.read frame.curveA = before.1.read frame.curveA ∧
      CoordinateValue curve (returned.read (rowRead frame.x destination))
        (returned.read (rowRead frame.y destination)) ((2 ^ (extra + 1)) • point) := by
  let first := frame.doubleRecord curve.field source destination environment before
  have firstModulus := frame.doubleRecord_read_modulus curve.field source destination environment
    before
  have firstCurve := frame.doubleRecord_read_curveA curve.field source destination environment
    before
  have firstValue := frame.doubleRecord_coordinateValue curve source destination environment
    before point loaded curveValue input
    (by simpa only [pow_zero, one_nsmul] using
      pow_two_nsmul_double_ne_zero point order 0 prime large original)
  have rest := frame.repeatedDoubleRecord_values curve destination extra environment first.1
    (point + point) order prime large (double_addOrderOf point order prime large original)
    (firstModulus.trans loaded) (by rw [firstCurve]; exact curveValue) firstValue
  dsimp only
  rw [frame.successiveRecord_state]
  have finalValue := rest.2.2
  rw [pow_two_nsmul_double] at finalValue
  exact ⟨rest.1.trans firstModulus, rest.2.1.trans firstCurve, finalValue⟩

/-- Every unvisited original array row survives the arbitrary-count real record. -/
lemma successiveRecord_read_other_row (spec : ModulusSpec width) (source destination : Fin length)
    (extra : Nat) (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ destination) :
    (frame.successiveRecord spec source destination extra environment before).1.1.read
      (rowRead array row) = before.1.read (rowRead array row) := by
  let first := frame.doubleRecord spec source destination environment before
  rw [frame.successiveRecord_state]
  exact (frame.repeatedDoubleRecord_read_other_row spec destination extra environment first.1
    array row different).trans
      (frame.doubleRecord_read_other_row spec source destination environment before array row
        different)

/-- The original sixteen-doubling specialization gives the same exact original group value. -/
lemma baseStepRecord_values (curve : CurveSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (input : CoordinateValue curve (before.1.read (rowRead frame.x source))
      (before.1.read (rowRead frame.y source)) point) :
    let returned := (frame.baseStepRecord curve.field source destination environment before).1.1
    returned.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      returned.read frame.curveA = before.1.read frame.curveA ∧
      CoordinateValue curve (returned.read (rowRead frame.x destination))
        (returned.read (rowRead frame.y destination)) ((2 ^ 16) • point) := by
  dsimp only
  rw [frame.baseStepRecord_state]
  exact frame.successiveRecord_values curve source destination 15 environment before point order
    prime large original loaded curveValue input

/-- Every original unvisited array row survives the original sixteen-doubling record. -/
lemma baseStepRecord_read_other_row (spec : ModulusSpec width) (source destination : Fin length)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ destination) :
    (frame.baseStepRecord spec source destination environment before).1.1.read
      (rowRead array row) = before.1.read (rowRead array row) := by
  rw [frame.baseStepRecord_state]
  exact frame.successiveRecord_read_other_row spec source destination 15 environment before array
    row different

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
