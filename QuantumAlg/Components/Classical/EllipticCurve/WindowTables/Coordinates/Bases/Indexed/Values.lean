/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Indexed
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Repeat
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Seed

/-!
# Group values and full complement retention for mapped small-base rows

The same actual program writes only its injective static row family.
Every selected row has its original power-of-two group value and every
unselected actual array word survives, including the other point family.
No bound on the unreduced two-to-256 scalar is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length baseCount : Nat}
  (frame : CoordinateFrame ctx width length)

private lemma indexed_base_scalar {G : Type*} [AddGroup G] (point : G) (count : Nat) :
    (2 ^ 16) • ((2 ^ (16 * count)) • point) = (2 ^ (16 * (count + 1))) • point := by
  rw [← mul_nsmul, ← pow_add]
  congr 2

/-- Every mapped row in the actual returned Store represents its original window-base point. -/
lemma prepareBasesAtRecord_values (curve : CurveSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) (injective : Function.Injective rows)
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (yFree : frame.x.key ∉ sourceY.storageKeys)
    (input : CoordinateValue curve (before.1.read sourceX) (before.1.read sourceY) point) :
    let returned := (frame.prepareBasesAtRecord curve.field sourceX sourceY rows environment
      before).1.1
    returned.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      returned.read frame.curveA = before.1.read frame.curveA ∧
      ∀ index : Fin (baseCount + 1), CoordinateValue curve
        (returned.read (rowRead frame.x (rows index)))
        (returned.read (rowRead frame.y (rows index))) ((2 ^ (16 * index.val)) • point) := by
  let zero : Fin (baseCount + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let seeded := frame.seedRecord (model := model) sourceX sourceY (rows zero) before
  have seedModulus : seeded.1.1.read (wordRead frame.modulus) =
      before.1.read (wordRead frame.modulus) := by
    apply frame.seedRecord_read_other
    · change frame.x.key ∉ [frame.modulus.key]
      simpa only [List.mem_singleton] using
        Ne.symm (modulus_array_key_ne frame.modulus frame.x)
    · change frame.y.key ∉ [frame.modulus.key]
      simpa only [List.mem_singleton] using
        Ne.symm (modulus_array_key_ne frame.modulus frame.y)
  have seedCurve : seeded.1.1.read frame.curveA = before.1.read frame.curveA :=
    frame.seedRecord_read_other sourceX sourceY (rows zero) before frame.curveA
      (frame.protectedCoefficient _ (by simp)) (frame.protectedCoefficient _ (by simp))
  have seedValue := frame.seedRecord_coordinateValue curve sourceX sourceY (rows zero) before point
    yFree input
  let invariant := fun processed (current : Store ctx × model.HiddenState) =>
    current.1.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      current.1.read frame.curveA = before.1.read frame.curveA ∧
      ∀ index : Fin (baseCount + 1), index.val ≤ processed → CoordinateValue curve
        (current.1.read (rowRead frame.x (rows index)))
        (current.1.read (rowRead frame.y (rows index))) ((2 ^ (16 * index.val)) • point)
  have initial : invariant 0 seeded.1 := by
    refine ⟨seedModulus, seedCurve, ?_⟩
    intro index visited
    have same : index = zero := Fin.ext (by change index.val = 0; omega)
    subst index
    simpa only [zero, Nat.mul_zero, pow_zero, one_nsmul] using seedValue
  have completed := Circuit.forRangeRecord_invariant baseCount
    (fun index => frame.baseStep curve.field (rows index.castSucc) (rows index.succ))
    (fun index => frame.baseStepRecord curve.field (rows index.castSucc) (rows index.succ)
      environment)
    invariant (fun index current established => by
      have step := frame.baseStepRecord_values curve (rows index.castSucc) (rows index.succ)
        environment current ((2 ^ (16 * index.val)) • point) order prime large
        (pow_two_nsmul_addOrderOf point order (16 * index.val) prime large original)
        (established.1.trans loaded) (by rw [established.2.1]; exact curveValue)
        (established.2.2 index.castSucc (Nat.le_refl _))
      refine ⟨step.1.trans established.1, step.2.1.trans established.2.1, ?_⟩
      intro queried visited
      by_cases same : queried = index.succ
      · subst queried
        simpa only [Fin.val_succ, indexed_base_scalar] using step.2.2
      · have different : rows queried ≠ rows index.succ := fun equal => same (injective equal)
        rw [frame.baseStepRecord_read_other_row curve.field (rows index.castSucc) (rows index.succ)
          environment current frame.x (rows queried) different,
          frame.baseStepRecord_read_other_row curve.field (rows index.castSucc) (rows index.succ)
            environment current frame.y (rows queried) different]
        exact established.2.2 queried (by
          have unequal : queried.val ≠ index.val + 1 := fun equal => same (Fin.ext equal)
          omega)) seeded.1 initial
  exact ⟨completed.1, completed.2.1, fun index => completed.2.2 index (by omega)⟩

/-- Every actual word outside the selected family, including the other point family, survives. -/
lemma prepareBasesAtRecord_read_outside (spec : ModulusSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (rows : Fin (baseCount + 1) → Fin length) (environment : model.Environment)
    (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width))) (row : Fin length)
    (outside : ∀ index, row ≠ rows index) :
    (frame.prepareBasesAtRecord spec sourceX sourceY rows environment before).1.1.read
      (rowRead array row) = before.1.read (rowRead array row) := by
  let seeded := frame.seedRecord (model := model) sourceX sourceY
    (rows ⟨0, Nat.zero_lt_succ _⟩) before
  have first := frame.seedRecord_read_other_row sourceX sourceY
    (rows ⟨0, Nat.zero_lt_succ _⟩) before array row (outside _)
  exact Circuit.forRangeRecord_invariant baseCount
    (fun index => frame.baseStep spec (rows index.castSucc) (rows index.succ))
    (fun index => frame.baseStepRecord spec (rows index.castSucc) (rows index.succ) environment)
    (fun _ current => current.1.read (rowRead array row) = before.1.read (rowRead array row))
    (fun index current established =>
      (frame.baseStepRecord_read_other_row spec (rows index.castSucc) (rows index.succ)
        environment current array row (outside _)).trans established) seeded.1 first

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
