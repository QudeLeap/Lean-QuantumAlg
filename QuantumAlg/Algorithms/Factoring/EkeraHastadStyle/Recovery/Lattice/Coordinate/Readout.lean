/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Coordinate
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Exact stored arithmetic of the native lattice coordinate update

The temporary multiplication preserves every original read, including when
either multiplicand is the target itself. The subsequent subtraction uses
that stored product and the original target value. Release exposes exactly
the resulting low word and leaves every other structural input unchanged.
All widths, including zero, use the same two actual instructions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem fresh_free {shape : CShape} (other : CInputRef ctx shape) (width : Nat) :
    ctx.canonicalFreshKey ∉ (underRead other width).storageKeys := by
  have support := CInputRef.storageKeys_underWorkspace other ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh
  exact fun present => ctx.canonicalFreshKey_fresh
    (other.storageKeys_subset_context (support ▸ present))

/-- The multiplication preserves every original stored value before target subtraction. -/
theorem nativeLattice_coordinate_multiply_read_other
    (coefficient source : CInputRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (store : Store (context ctx width)) :
    (store.applyOp (multiplyOp coefficient source)).read (underRead other width) =
      store.read (underRead other width) :=
  Store.read_applyOp_of_not_mem_storageKeys store (multiplyOp coefficient source)
    (underRead other width) (fresh_free other width)

/-- The actual scratch word holds the low product of the actual pre-update operand values. -/
theorem nativeLattice_coordinate_product_read
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (store : Store (context ctx width)) :
    ((store.applyOp (multiplyOp coefficient source)).read
      (.storage (product ctx width).toCStorageRef)).toNat =
        ((store.read (underRead coefficient width)).toNat *
          (store.read (underRead source width)).toNat) % 2 ^ width := by
  exact congrArg CShape.Value.toNat
    (Store.read_applyOp_output store (multiplyOp coefficient source))

/-- The two actual instructions implement the original wrapping multiply-subtract coordinate. -/
theorem nativeLattice_coordinate_read
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((storeStep coefficient source target store).read (.storage target.toCStorageRef)).toNat =
      ((store.read (.storage target.toCStorageRef)).toNat + 2 ^ width -
        ((store.read coefficient).toNat * (store.read source).toNat) % 2 ^ width) % 2 ^ width := by
  let entered : Store (context ctx width) := store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let multiplied : Store (context ctx width) := entered.applyOp (multiplyOp coefficient source)
  have targetRead : (multiplied.read
      (underRead (.storage target.toCStorageRef) width)).toNat =
        (store.read (.storage target.toCStorageRef)).toNat :=
    congrArg CShape.Value.toNat
      ((nativeLattice_coordinate_multiply_read_other coefficient source
        (.storage target.toCStorageRef) entered).trans
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
          (.unsignedWord width) ctx.canonicalFreshKey_fresh (.storage target.toCStorageRef)))
  have productRead : (multiplied.read (.storage (product ctx width).toCStorageRef)).toNat =
      ((store.read coefficient).toNat * (store.read source).toNat) % 2 ^ width :=
    (nativeLattice_coordinate_product_read coefficient source entered).trans
      (congrArg₂ (fun (left right : CShape.Value (.unsignedWord width)) =>
        (left.toNat * right.toNat) % 2 ^ width)
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
          (.unsignedWord width) ctx.canonicalFreshKey_fresh coefficient)
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
          (.unsignedWord width) ctx.canonicalFreshKey_fresh source))
  have subtraction := congrArg CShape.Value.toNat
    (Store.read_applyOp_output multiplied (subtractOp target))
  have released := congrArg CShape.Value.toNat
    (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh (bodyStore coefficient source target entered)
      (.storage target.toCStorageRef))
  exact released.trans (subtraction.trans
    (congrArg₂ (fun old product : Nat => (old + 2 ^ width - product) % 2 ^ width)
      targetRead productRead))

/-- Every other original structural read survives the complete actual coordinate update. -/
theorem nativeLattice_coordinate_read_other
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (different : target.key ∉ other.storageKeys) (store : Store ctx) :
    (storeStep coefficient source target store).read other = store.read other := by
  let entered : Store (context ctx width) := store.pushWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh
  have underDifferent : target.key ∉ (underRead other width).storageKeys :=
    fun present => different ((CInputRef.storageKeys_underWorkspace other ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh) ▸ present)
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (bodyStore coefficient source target entered) other).trans
    ((Store.read_applyOp_of_not_mem_storageKeys (entered.applyOp (multiplyOp coefficient source))
      (subtractOp target) (underRead other width) underDifferent).trans
      ((nativeLattice_coordinate_multiply_read_other coefficient source other entered).trans
        (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.unsignedWord width)
          ctx.canonicalFreshKey_fresh other)))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate
