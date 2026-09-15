/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Reindex

/-!
# Independent measurement cells and their actual allocation semantics

Distinct indexed cells have distinct live storage keys. Writing one therefore
preserves every other cell. Allocation preserves the complete quantum matrix,
including its reference correlations, and restores the entire borrowed
classical-quantum-reference observation. The coordinate maps follow only the
unchanged quantum wires at each actual classical allocation.
-/

namespace QuantumAlg.Execution.MeasurementCells

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

private theorem reference_key_mem {ctx : RuntimeCtx kind} {shape : CShape}
    (ref : CStorageRef ctx shape) : ref.key ∈ ctx.keys :=
  List.mem_map.mpr ⟨.storage ref.key ref.role shape, ref.present, rfl⟩

/-- Indexed cells occupy different live storage identities. -/
theorem reference_key_injective (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    Function.Injective (fun index => (reference ctx dimension count index).key) := by
  induction count with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right same
      revert same
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          change (context ctx dimension count).canonicalFreshKey =
            (reference ctx dimension count right).key at same
          have present := reference_key_mem (reference ctx dimension count right).toCStorageRef
          exact False.elim ((context ctx dimension count).canonicalFreshKey_fresh
            (same.symm ▸ present))
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          change (reference ctx dimension count left).key =
            (context ctx dimension count).canonicalFreshKey at same
          have present := reference_key_mem (reference ctx dimension count left).toCStorageRef
          exact False.elim ((context ctx dimension count).canonicalFreshKey_fresh
            (same ▸ present))
        · intro same
          exact congrArg Fin.succ (ih same)

/-- Writing the selected cell reads back its exact finite value. -/
theorem read_write_reference_same (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (store : Store (context ctx dimension count)) (index : Fin count) (value : Fin dimension) :
    (store.write (reference ctx dimension count index) (.finite value)).read
      (.storage (reference ctx dimension count index).toCStorageRef) = .finite value :=
  Store.read_write_same store _ _

/-- Writing one measurement cell preserves every differently indexed cell. -/
theorem read_write_reference_other (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (store : Store (context ctx dimension count)) (written observed : Fin count)
    (different : written ≠ observed) (value : Fin dimension) :
    (store.write (reference ctx dimension count written) (.finite value)).read
      (.storage (reference ctx dimension count observed).toCStorageRef) =
        store.read (.storage (reference ctx dimension count observed).toCStorageRef) :=
  Store.read_write_other store _ _ _
    (fun same => different (reference_key_injective ctx dimension count same))

/-- Quantum wire positions pass unchanged through every actual retained-cell extension. -/
def wireEquiv (ctx : RuntimeCtx kind) (dimension : ℕ+) :
    (count : Nat) → Fin ctx.systemCount ≃ Fin (context ctx dimension count).systemCount
  | 0 => Equiv.refl _
  | count + 1 => wireEquiv ctx dimension count

/-- Corresponding positions keep both their physical identity and their local dimension. -/
theorem wireEquiv_preserved (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (wire : Fin ctx.systemCount) :
    (context ctx dimension count).quantumLayout.wire (wireEquiv ctx dimension count wire) =
      ctx.quantumLayout.wire wire := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- The whole basis follows the same actual, unchanged wire frame. -/
def basisEquiv (ctx : RuntimeCtx kind) (dimension : ℕ+) :
    (count : Nat) → ctx.register.Index ≃ (context ctx dimension count).register.Index
  | 0 => Equiv.refl _
  | count + 1 => basisEquiv ctx dimension count

/-- Each finite physical basis value is unchanged by the classical allocations. -/
theorem basisEquiv_value (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (basis : ctx.register.Index) (wire : Fin ctx.systemCount) :
    (basisEquiv ctx dimension count basis (wireEquiv ctx dimension count wire)).val =
      (basis wire).val := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- The same coordinate map leaves the external reference coordinate untouched. -/
def jointBasisEquiv (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    (Reference : Register) :
    (Register.prod ctx.register Reference).Index ≃
      (Register.prod (context ctx dimension count).register Reference).Index :=
  (basisEquiv ctx dimension count).prodCongr (Equiv.refl Reference.Index)

/-- The actual interpreter retains every quantum matrix entry and reference correlation. -/
theorem allocate_quantumMarginal (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    ((allocate ctx dimension count).execute Reference state).quantumMarginal =
      state.quantumMarginal.reindex
        (S := Register.prod (context ctx dimension count).register Reference)
        (jointBasisEquiv ctx dimension count Reference) := by
  induction count with
  | zero =>
      rw [allocate, Circuit.execute_id, State.skip_quantumMarginal]
      exact (DensityOperator.reindex_refl state.quantumMarginal).symm
  | succ count ih =>
      change ((Circuit.seq (allocate ctx dimension count)
        (.retain (context ctx dimension count)
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh)).execute
            Reference state).quantumMarginal = _
      rw [Circuit.execute_seq, State.mapHistory_quantumMarginal]
      change (State.retain ((allocate ctx dimension count).execute Reference state)
        (context ctx dimension count).canonicalFreshKey (.finite dimension)
        (context ctx dimension count).canonicalFreshKey_fresh).quantumMarginal = _
      rw [State.retain_quantumMarginal]
      exact ih

/-- Every retained-cell allocation restores the full original borrowed interface. -/
theorem allocate_borrowedRestored (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H) :
    (allocate ctx dimension count).BorrowedRestored Reference state
      ((allocate ctx dimension count).execute Reference state) := by
  induction count with
  | zero =>
      change observeBorrowed Reference state.skip = observeBorrowed Reference state
      exact observeBorrowed_mapHistory state (fun history => (history, ()))
  | succ count ih =>
      exact Circuit.borrowedRestored_seq _ _ state ih
        (Circuit.borrowedRestored_retain
          (context ctx dimension count).canonicalFreshKey (.finite dimension)
          (context ctx dimension count).canonicalFreshKey_fresh
          ((allocate ctx dimension count).execute Reference state))

end

end QuantumAlg.Execution.MeasurementCells
