/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Construction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reset
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stage
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context.Coordinates
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Feedback.Carrier
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Core.Execution.Store.WritePrefix
import all QuantumAlg.Core.Execution.Store

/-!
# Actual stored outputs and earlier-bit feedback

Core Store.WritePrefix is reused directly.
The actual measured stage writes its own output after the dimension cast. All
retained output values are proved using distinct physical keys. Earlier-bit
feedback then agrees with the chronological record while arbitrary future
and unrelated old cell values remain unrestricted. No packing is executed here.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.StoredOutputs

noncomputable section

open Execution

private lemma finite_write_cast {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {dimension : ℕ+} (same : dimension = 2) (store : Store ctx)
    (output : CWriteRef ctx (.finite 2)) (outcome : Fin 2) :
    store.write (Eq.mpr (congrArg (fun d => CWriteRef ctx (.finite d)) same) output)
        (.finite (Fin.cast (congrArg PNat.val same).symm outcome)) =
      store.write output (.finite outcome) := by
  subst dimension
  rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The actual dimensioned output write is exactly the same real binary storage update. -/
lemma dimensioned_write (store : Store (Context base noQuantum m ell width))
    (output : CWriteRef (Context base noQuantum m ell width) (.finite 2)) (outcome : Fin 2) :
    store.write (dimensionedCell base noQuantum m ell width output)
        (.finite (ContextCoordinates.physicalBit base noQuantum m ell width outcome)) =
      store.write output (.finite outcome) := by
  simpa only [dimensionedCell, ContextCoordinates.physicalBit] using
    finite_write_cast (control_qubit base noQuantum m ell width) store output outcome

/-- Preparation, branch history and reset do not add any further classical write. -/
lemma stageRecord_store (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Fin bits) {History : Type}
    (source : Store (Context base noQuantum m ell width) × (model.HiddenState × History))
    (outcome : Fin 2) :
    (stageRecord base noQuantum m ell width inverse outputs N unit position source
        (ContextCoordinates.physicalBit base noQuantum m ell width outcome)).1 =
      source.1.write (outputs position) (.finite outcome) := by
  change source.1.write (dimensionedCell base noQuantum m ell width (outputs position))
    (.finite (ContextCoordinates.physicalBit base noQuantum m ell width outcome)) = _
  exact dimensioned_write base noQuantum m ell width source.1 (outputs position) outcome

def outcomeStore {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (count : Nat) (bounded : count ≤ bits) : Store (Context base noQuantum m ell width) :=
  Store.writePrefix outputs (fun index => .finite (record index)) original count bounded

/-- Every already measured physical cell retains its own value despite later output writes. -/
lemma outcomeStore_read {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (count : Nat) (bounded : count ≤ bits) (index : Fin bits) (written : index.val < count) :
    (outcomeStore base noQuantum m ell width outputs record original count bounded).read
      (.storage (outputs index).toCStorageRef) = .finite (record index) :=
  Store.read_writePrefix outputs (fun index => .finite (record index)) separate original count
    bounded index written

/-- This proves retention of all n actual binary cells, without an integer packing instruction. -/
lemma outcomeStore_all_read {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (index : Fin bits) :
    (outcomeStore base noQuantum m ell width outputs record original bits le_rfl).read
      (.storage (outputs index).toCStorageRef) = .finite (record index) :=
  Store.read_writePrefix_all outputs (fun index => .finite (record index)) separate original index

/-- Feedback after the real earlier writes uses exactly those bits of the chronological record. -/
lemma angle_after_prefix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val) :
    FeedbackCarrier.angle base noQuantum m ell width inverse outputs position count bounded
        (outcomeStore base noQuantum m ell width outputs record original position.val
          (Nat.le_of_lt position.isLt)) =
      Trajectory.feedbackAngle inverse record position count bounded := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [FeedbackCarrier.angle, Trajectory.feedbackAngle, induction]
      rw [outcomeStore_read base noQuantum m ell width outputs separate record original
        position.val (Nat.le_of_lt position.isLt)
        ⟨count, by have bound := position.isLt; omega⟩ (Nat.lt_of_succ_le bounded)]
      rfl

/-- The phase in the actual clean Kraus branch is therefore the record's original source phase. -/
lemma scalar_after_prefix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : Function.Injective (fun index => (outputs index).key))
    (record : Fin bits → Fin 2) (original : Store (Context base noQuantum m ell width))
    (position : Fin bits) :
    FeedbackCarrier.scalar base noQuantum m ell width inverse outputs position position.val le_rfl
        (outcomeStore base noQuantum m ell width outputs record original position.val
          (Nat.le_of_lt position.isLt)) =
      Complex.exp ((Trajectory.feedbackAngle inverse record position position.val le_rfl : ℂ) *
        Complex.I) := by
  rw [FeedbackCarrier.scalar_eq_exp,
    angle_after_prefix base noQuantum m ell width inverse outputs separate record original position
      position.val le_rfl]

/-- Actual canonical allocation supplies physical-key distinctness for the complete member. -/
lemma canonical_outputs_read (record : Fin (resultBits m ell) → Fin 2)
    (original : Store (Context base noQuantum m ell width)) (index : Fin (resultBits m ell)) :
    (outcomeStore base noQuantum m ell width (cells base noQuantum m ell width) record original
      (resultBits m ell) le_rfl).read
        (.storage (cells base noQuantum m ell width index).toCStorageRef) =
          .finite (record index) :=
  outcomeStore_all_read base noQuantum m ell width (cells base noQuantum m ell width)
    (cells_distinct base noQuantum m ell width) record original index

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.StoredOutputs
