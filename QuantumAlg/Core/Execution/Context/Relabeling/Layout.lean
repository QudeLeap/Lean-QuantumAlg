/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.Context.Relabeling
import Mathlib.Logic.Equiv.Basic

/-!
# Finite basis values on injectively placed physical systems

The context mapping retains the complete ordered wire list. Each corresponding
position has its prescribed new physical identity and its original positive
dimension. The basis equivalence follows these positions and retains the exact
finite value on each system, including nonbinary systems.
-/

namespace QuantumAlg.Execution.ContextRelabeling

variable {kind : ProblemKind} (ctx : RuntimeCtx kind)
  (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)

/-- The corresponding position retains its ordinal in the complete mapped wire list. -/
def positions : Fin ctx.systemCount ≃ Fin (ctx.relabel keys physical).systemCount :=
  finCongr (ctx.relabel_systemCount keys physical).symm

/-- Corresponding systems have exactly the prescribed identity and original dimension. -/
lemma positions_wire (index : Fin ctx.systemCount) :
    (ctx.relabel keys physical).quantumLayout.wire (positions ctx keys physical index) =
      QuantumWire.relabel physical (ctx.quantumLayout.wire index) := by
  have mappedBound : index.val < (ctx.relabel keys physical).quantumWires.length := by
    rw [RuntimeCtx.relabel_quantumWires, List.length_map]
    exact index.isLt
  change (ctx.relabel keys physical).quantumWires[index.val]'mappedBound =
    QuantumWire.relabel physical ctx.quantumWires[index.val]
  simp only [RuntimeCtx.relabel_quantumWires, List.getElem_map]

/-- No physical placement changes a system's native finite dimension. -/
lemma positions_dimension (index : Fin ctx.systemCount) :
    ((ctx.relabel keys physical).quantumLayout.wire
      (positions ctx keys physical index)).dimension =
        (ctx.quantumLayout.wire index).dimension := by
  simpa only [QuantumWire.relabel] using
    congrArg QuantumWire.dimension (positions_wire ctx keys physical index)

/-- Re-express all original finite values on their mapped physical systems. -/
def basis : ctx.register.Index ≃ (ctx.relabel keys physical).register.Index :=
  (positions ctx keys physical).piCongr fun index =>
    finCongr (congrArg PNat.val (positions_dimension ctx keys physical index).symm)

/-- The exact finite value at every mapped physical system is unchanged. -/
lemma basis_value (value : ctx.register.Index) (index : Fin ctx.systemCount) :
    (basis ctx keys physical value (positions ctx keys physical index)).val =
      (value index).val := by
  exact congrArg
    (fun result : Fin ((ctx.relabel keys physical).quantumLayout.wire
      (positions ctx keys physical index)).dimension => result.val)
    (Equiv.piCongr_apply_apply
      (W := fun position : Fin ctx.systemCount => Fin (ctx.quantumLayout.wire position).dimension)
      (Z := fun position : Fin (ctx.relabel keys physical).systemCount =>
        Fin ((ctx.relabel keys physical).quantumLayout.wire position).dimension)
      (positions ctx keys physical)
      (fun position =>
        finCongr (congrArg PNat.val (positions_dimension ctx keys physical position).symm))
      value index)

end QuantumAlg.Execution.ContextRelabeling
