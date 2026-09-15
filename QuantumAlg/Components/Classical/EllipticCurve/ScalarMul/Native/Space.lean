/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Resources

/-!
# Actual live storage of the original scalar program

Initialization releases its original three cells before the scalar slots.
Each complete addition likewise releases its internal cells before the next
call. The genuinely retained point is charged throughout both native space
projections; the caller's entire resident and auxiliary context is retained.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- Only initialization or one complete addition has an active internal scope at a time. -/
def scalarScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (((Add.Native.infinityShapes width).map SpacePool.ofShape).sum)
    (Add.Native.additionScratchSpace kind width)

private theorem scalarBitArm_resident_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (path : (scalarBitArm spec point accumulator value).Path) :
    (scalarBitArm spec point accumulator value).peakResidentSpace path ≤
      Add.Native.additionScratchSpace kind width + ctx.residentSpace := by
  cases value with
  | bit flag =>
      cases flag
      · change SpacePool.max ctx.residentSpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact fun axis => Nat.le_add_left _ _
      · exact Add.Native.addInto_resident_le spec _ point accumulator path

private theorem scalarSlot_resident_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (path : (scalarSlot spec bits point accumulator index).Path) :
    (scalarSlot spec bits point accumulator index).peakResidentSpace path ≤
      Add.Native.additionScratchSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Add.Native.addInto spec (Add.Native.classifierRead accumulator)
      (Add.Native.classifierRead accumulator) accumulator)
    (.branch (.vectorGet bits index) (scalarBitArm spec point accumulator)) path).le.trans ?_
  exact SpacePool.max_le (Add.Native.addInto_resident_le spec _ _ accumulator path.1)
    (scalarBitArm_resident_le spec point accumulator path.2.1 path.2.2)

/-- Every actual scalar scope is covered with the entire original resident context. -/
theorem scalarInto_resident_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (path : (scalarInto spec bits point accumulator).Path) :
    (scalarInto spec bits point accumulator).peakResidentSpace path ≤
      scalarScratchSpace kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (Add.Native.infinityInto accumulator)
    (scalarFold spec bits point accumulator) path).le.trans ?_
  apply SpacePool.max_le
  · exact (Add.Native.infinityInto_resident accumulator path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (Circuit.forRange_resident_le scalarWidth (scalarSlot spec bits point accumulator)
      (Add.Native.additionScratchSpace kind width + ctx.residentSpace)
      (fun axis => Nat.le_add_left _ _) (scalarSlot_resident_le spec bits point accumulator)
      path.2).trans (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The real retained point remains charged alongside the complete resident scope allowance. -/
theorem scalarRetained_resident_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (scalarRetained spec bits point key fresh).Path) :
    (scalarRetained spec bits point key fresh).peakResidentSpace path ≤
      scalarScratchSpace kind width + SpacePool.ofShape (PointShape width) +
        ctx.residentSpace := by
  let body := scalarInto spec (bits.underRetained key (PointShape width) fresh)
    (point.underRetained key (PointShape width) fresh)
    (CWriteRef.retainedHead ctx key (PointShape width) fresh)
  have entered : (Circuit.retain ctx key (PointShape width) fresh).peakResidentSpace path.1 ≤
      (ctx.addRetained key (PointShape width) fresh).residentSpace := by
    change SpacePool.max ctx.residentSpace
      (SpacePool.max (ctx.addRetained key (PointShape width) fresh).residentSpace 0) ≤ _
    rw [SpacePool.max_zero]
    exact SpacePool.max_le (fun axis => Nat.le_add_left _ _) le_rfl
  have composed := Circuit.peakResidentSpace_seq
    (.retain ctx key (PointShape width) fresh) body path
  refine composed.le.trans ?_
  have budget : SpacePool.max
      ((Circuit.retain ctx key (PointShape width) fresh).peakResidentSpace path.1)
      (body.peakResidentSpace path.2) ≤
      scalarScratchSpace kind width +
        (ctx.addRetained key (PointShape width) fresh).residentSpace :=
    SpacePool.max_le (entered.trans (fun axis => Nat.le_add_left _ _))
      (scalarInto_resident_le spec _ _ _ path.2)
  simpa only [RuntimeCtx.residentSpace_addRetained, add_assoc] using budget

private theorem scalarBitArm_auxiliary_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (path : (scalarBitArm spec point accumulator value).Path) :
    (scalarBitArm spec point accumulator value).peakAuxiliarySpace path ≤
      Add.Native.additionScratchSpace kind width + ctx.auxiliarySpace := by
  cases value with
  | bit flag =>
      cases flag
      · change SpacePool.max ctx.auxiliarySpace 0 ≤ _
        rw [SpacePool.max_zero]
        exact fun axis => Nat.le_add_left _ _
      · exact Add.Native.addInto_auxiliary_le spec _ point accumulator path

private theorem scalarSlot_auxiliary_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (path : (scalarSlot spec bits point accumulator index).Path) :
    (scalarSlot spec bits point accumulator index).peakAuxiliarySpace path ≤
      Add.Native.additionScratchSpace kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Add.Native.addInto spec (Add.Native.classifierRead accumulator)
      (Add.Native.classifierRead accumulator) accumulator)
    (.branch (.vectorGet bits index) (scalarBitArm spec point accumulator)) path).le.trans ?_
  exact SpacePool.max_le (Add.Native.addInto_auxiliary_le spec _ _ accumulator path.1)
    (scalarBitArm_auxiliary_le spec point accumulator path.2.1 path.2.2)

/-- Every actual scalar scope is covered with the entire original auxiliary context. -/
theorem scalarInto_auxiliary_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (path : (scalarInto spec bits point accumulator).Path) :
    (scalarInto spec bits point accumulator).peakAuxiliarySpace path ≤
      scalarScratchSpace kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (Add.Native.infinityInto accumulator)
    (scalarFold spec bits point accumulator) path).le.trans ?_
  apply SpacePool.max_le
  · exact (Add.Native.infinityInto_auxiliary accumulator path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (Circuit.forRange_auxiliary_le scalarWidth (scalarSlot spec bits point accumulator)
      (Add.Native.additionScratchSpace kind width + ctx.auxiliarySpace)
      (fun axis => Nat.le_add_left _ _) (scalarSlot_auxiliary_le spec bits point accumulator)
      path.2).trans (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- The real retained point remains charged alongside the complete auxiliary scope allowance. -/
theorem scalarRetained_auxiliary_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (scalarRetained spec bits point key fresh).Path) :
    (scalarRetained spec bits point key fresh).peakAuxiliarySpace path ≤
      scalarScratchSpace kind width + SpacePool.ofShape (PointShape width) +
        ctx.auxiliarySpace := by
  let body := scalarInto spec (bits.underRetained key (PointShape width) fresh)
    (point.underRetained key (PointShape width) fresh)
    (CWriteRef.retainedHead ctx key (PointShape width) fresh)
  have entered : (Circuit.retain ctx key (PointShape width) fresh).peakAuxiliarySpace path.1 ≤
      (ctx.addRetained key (PointShape width) fresh).auxiliarySpace := by
    change SpacePool.max ctx.auxiliarySpace
      (SpacePool.max (ctx.addRetained key (PointShape width) fresh).auxiliarySpace 0) ≤ _
    rw [SpacePool.max_zero]
    exact SpacePool.max_le (fun axis => Nat.le_add_left _ _) le_rfl
  have composed := Circuit.peakAuxiliarySpace_seq
    (.retain ctx key (PointShape width) fresh) body path
  refine composed.le.trans ?_
  have budget : SpacePool.max
      ((Circuit.retain ctx key (PointShape width) fresh).peakAuxiliarySpace path.1)
      (body.peakAuxiliarySpace path.2) ≤
      scalarScratchSpace kind width +
        (ctx.addRetained key (PointShape width) fresh).auxiliarySpace :=
    SpacePool.max_le (entered.trans (fun axis => Nat.le_add_left _ _))
      (scalarInto_auxiliary_le spec _ _ _ path.2)
  simpa only [RuntimeCtx.auxiliarySpace_addRetained, add_assoc] using budget

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
