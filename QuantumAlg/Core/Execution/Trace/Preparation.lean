/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Exact live-space peaks of actual quantum preparation

An actual preparation adds an owned physical layout and retains every old
entry. Its visited-context peak is therefore exactly its complete post-context,
separately for resident and fixed-role auxiliary storage.
-/

namespace QuantumAlg.Circuit

open Execution

variable {count : Nat} (ctx : RuntimeCtx .quantum) (key : StorageKey)
  (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
  (preparation : BasisPreparation layout)

/-- Every newly prepared system and every old entry contribute to the actual resident peak. -/
theorem prepare_peakResidentSpace
    (path : (Circuit.prepare ctx key layout fresh disjoint preparation).Path) :
    (Circuit.prepare ctx key layout fresh disjoint preparation).peakResidentSpace path =
      (ctx.addOwnedLayout key layout fresh disjoint).residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max (ctx.addOwnedLayout key layout fresh disjoint).residentSpace 0) = _
  rw [SpacePool.max_zero]
  apply SpacePool.max_eq_right
  rw [RuntimeCtx.residentSpace_addOwnedLayout]
  exact fun axis => Nat.le_add_left (ctx.residentSpace axis) (SpacePool.ofQuantumLayout layout axis)

/-- The actual auxiliary peak retains all original roles and the new owned preparation bank. -/
theorem prepare_peakAuxiliarySpace
    (path : (Circuit.prepare ctx key layout fresh disjoint preparation).Path) :
    (Circuit.prepare ctx key layout fresh disjoint preparation).peakAuxiliarySpace path =
      (ctx.addOwnedLayout key layout fresh disjoint).auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max (ctx.addOwnedLayout key layout fresh disjoint).auxiliarySpace 0) = _
  rw [SpacePool.max_zero]
  apply SpacePool.max_eq_right
  rw [RuntimeCtx.auxiliarySpace_addOwnedLayout]
  exact fun axis =>
    Nat.le_add_left (ctx.auxiliarySpace axis) (SpacePool.ofQuantumLayout layout axis)

end QuantumAlg.Circuit
