/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Repeat
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Seed

/-!
# All original group values of the actual two small-base arrays

The complete existing base-preparation record starts with its two real
copies, then advances each physical destination by sixteen paid doublings.
Every completed original row is retained. The prime-order argument works
for all powers of two, including the final two-to-256 scalar.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width baseCount : Nat}
  (frame : CoordinateFrame ctx width (baseCount + 1))

private lemma next_base_scalar {G : Type*} [AddGroup G] (point : G) (count : Nat) :
    (2 ^ 16) • ((2 ^ (16 * count)) • point) = (2 ^ (16 * (count + 1))) • point := by
  rw [← mul_nsmul, ← pow_add]
  congr 2

/-- Every small-base coordinate pair in the real returned Store has its original group value. -/
lemma prepareBasesRecord_values (curve : CurveSpec width)
    (sourceX sourceY : CInputRef ctx (.unsignedWord width))
    (environment : model.Environment) (before : Store ctx × model.HiddenState)
    (point : Point curve) (order : Nat) (prime : order.Prime) (large : 3 < order)
    (original : addOrderOf point = order)
    (loaded : before.1.read (wordRead frame.modulus) = .unsignedWord curve.field.extendedWord)
    (curveValue : ((before.1.read frame.curveA).toNat : ZMod curve.field.modulus) = curve.curve.a)
    (yFree : frame.x.key ∉ sourceY.storageKeys)
    (input : CoordinateValue curve (before.1.read sourceX) (before.1.read sourceY) point) :
    let returned := (frame.prepareBasesRecord curve.field sourceX sourceY environment before).1.1
    returned.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      returned.read frame.curveA = before.1.read frame.curveA ∧
      ∀ row : Fin (baseCount + 1), CoordinateValue curve
        (returned.read (rowRead frame.x row)) (returned.read (rowRead frame.y row))
        ((2 ^ (16 * row.val)) • point) := by
  let zero : Fin (baseCount + 1) := ⟨0, Nat.zero_lt_succ _⟩
  let seeded := frame.seedRecord (model := model) sourceX sourceY zero before
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
    frame.seedRecord_read_other sourceX sourceY zero before frame.curveA
      (frame.protectedCoefficient _ (by simp)) (frame.protectedCoefficient _ (by simp))
  have seedValue := frame.seedRecord_coordinateValue curve sourceX sourceY zero before point
    yFree input
  let invariant := fun processed (current : Store ctx × model.HiddenState) =>
    current.1.read (wordRead frame.modulus) = before.1.read (wordRead frame.modulus) ∧
      current.1.read frame.curveA = before.1.read frame.curveA ∧
      ∀ row : Fin (baseCount + 1), row.val ≤ processed → CoordinateValue curve
        (current.1.read (rowRead frame.x row)) (current.1.read (rowRead frame.y row))
        ((2 ^ (16 * row.val)) • point)
  have initial : invariant 0 seeded.1 := by
    refine ⟨seedModulus, seedCurve, ?_⟩
    intro row visited
    have same : row = zero := Fin.ext (by change row.val = 0; omega)
    subst row
    simpa only [zero, Nat.mul_zero, pow_zero, one_nsmul] using seedValue
  have completed := Circuit.forRangeRecord_invariant baseCount
    (fun index => frame.baseStep curve.field index.castSucc index.succ)
    (fun index => frame.baseStepRecord curve.field index.castSucc index.succ environment)
    invariant (fun index current established => by
      have step := frame.baseStepRecord_values curve index.castSucc index.succ environment current
        ((2 ^ (16 * index.val)) • point) order prime large
        (pow_two_nsmul_addOrderOf point order (16 * index.val) prime large original)
        (established.1.trans loaded) (by rw [established.2.1]; exact curveValue)
        (established.2.2 index.castSucc (Nat.le_refl _))
      refine ⟨step.1.trans established.1, step.2.1.trans established.2.1, ?_⟩
      intro row visited
      by_cases same : row = index.succ
      · subst row
        simpa only [Fin.val_succ, next_base_scalar] using step.2.2
      · rw [frame.baseStepRecord_read_other_row curve.field index.castSucc index.succ environment
          current frame.x row same,
          frame.baseStepRecord_read_other_row curve.field index.castSucc index.succ environment
            current frame.y row same]
        exact established.2.2 row (by
          have different : row.val ≠ index.val + 1 := fun equal => same (Fin.ext equal)
          omega)) seeded.1 initial
  exact ⟨completed.1, completed.2.1, fun row => completed.2.2 row (by omega)⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.CoordinateFrame
