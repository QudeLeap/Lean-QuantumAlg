/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.GateModel.Algorithm

/-!
# Actual internal preparation of the shared-EEA Ctrl wire

Ctrl is the fifth allocated source control, following both shared words,
all four lengths, and the four phase/sign/parity bits
[LYL+26, sec_EEA/sub_regshare.tex:16-26]. This internal preparation stage
takes those preceding physical systems in an arbitrary joint state and
allocates precisely the missing Ctrl system in basis zero. It uses the
single `Circuit.prepareZero` instruction, with its actual native event and
space extension.

All old context-reference matrix entries are preserved, with no separation
or cleanliness requirement on the old state. The new zero support follows
from the real preparation, rather than an input-side clean-Ctrl premise
[dW19, qcnotes.tex:5381,8071]. This is the Ctrl allocation stage only:
preparing the other work fields, computing the input-dependent divisor
length, and folding the input are separate operations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ControlPreparation

noncomputable section

open Execution

/-- Every existing source wire before the final Ctrl position. -/
def bodyWidth (width : Nat) : Nat := 2 * (width + 3) + 4 * width.size + 4

/-- Internal context before allocating Ctrl; none of these prior values is constrained. -/
def before (width : Nat) : RuntimeCtx .quantum := OwnedQubits.context (bodyWidth width)

private def controlKey : StorageKey := ⟨1⟩

/-- Allocate the missing last physical identity, without changing any existing address. -/
def controlQubitLayout (width : Nat) : QubitLayout 1 where
  physical_idx index := bodyWidth width + index.val
  physical_idx_injective := by
    intro left right same
    apply Fin.ext
    change bodyWidth width + left.val = bodyWidth width + right.val at same
    omega

def controlLayout (width : Nat) : QuantumLayout 1 :=
  (controlQubitLayout width).toQuantumLayout

private theorem control_identities (width : Nat) :
    (controlLayout width).identities = [bodyWidth width] := rfl

private theorem control_fresh (width : Nat) : controlKey ∉ (before width).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

private theorem control_disjoint (width : Nat) :
    List.Disjoint (controlLayout width).identities (before width).physicalIdx := by
  rw [control_identities]
  change List.Disjoint [bodyWidth width] (OwnedQubits.context (bodyWidth width)).physicalIdx
  rw [OwnedQubits.ownedQubits_physicalIdx]
  apply List.disjoint_left.mpr
  intro wire new old
  have identity : wire = bodyWidth width := List.mem_singleton.mp new
  have prior := List.mem_range.mp old
  omega

/-- All source systems are live after this single missing-wire allocation. -/
def after (width : Nat) : RuntimeCtx .quantum :=
  (before width).addOwnedLayout controlKey (controlLayout width)
    (control_fresh width) (control_disjoint width)

/-- The preparation fixes zero on the newly allocated physical Ctrl system. -/
def preparation (width : Nat) : BasisPreparation (controlLayout width) :=
  BasisPreparation.zero (controlLayout width)

/-- The sole execution syntax allocates and prepares the actual missing source Ctrl. -/
def circuit (width : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty) (before width) (after width) :=
  .prepareZero (before width) controlKey (controlLayout width)
    (control_fresh width) (control_disjoint width)

/-- The fresh wire has exactly the physical identity of the native semantic Ctrl lens. -/
theorem control_identity (width : Nat) :
    (controlQubitLayout width).physical_idx 0 = (controlBit width).wire.val := by
  rw [controlBit_wire]
  rfl

/-- Preparing Ctrl completes precisely the previously declared full register width. -/
theorem complete_width (width : Nat) : bodyWidth width + 1 = (encoding width).width := by
  rw [encoding_width]
  unfold bodyWidth
  omega

/-- This stage allocates one actual dimension-two system. -/
theorem control_dimension (width : Nat) :
    ((controlLayout width).wire 0).dimension = 2 := rfl

/-- The preparation's actual finite value is zero on the declared control wire. -/
theorem prepared_control_zero (width : Nat) : (preparation width).value 0 = 0 := rfl

/-- The native preparation event is retained in every execution path. -/
theorem circuit_eventTrace (width : Nat) (path : (circuit width).Path) :
    (circuit width).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty (controlLayout width) := rfl

variable {Reference : Register} {H : Type} [Fintype H]

/-- Exact fresh/old/reference assembly through the actual newly allocated wire records. -/
def joined (width : Nat) (fresh : (controlLayout width).register.Index)
    (old : (Register.prod (before width).register Reference).Index) :
    (Register.prod (after width).register Reference).Index :=
  prepareContextBasisEquiv (before width) Reference controlKey (controlLayout width)
    (control_fresh width) (control_disjoint width) (fresh, old)

/-- Actual preparation retains every old joint coherence, including arbitrary external reference. -/
theorem execute_joined_entry (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (newRow newColumn : (controlLayout width).register.Index)
    (oldRow oldColumn : (Register.prod (before width).register Reference).Index) :
    ((circuit width).execute Reference state).quantumMarginal.matrix
      (joined width newRow oldRow) (joined width newColumn oldColumn) =
        ((preparation width).normalized.vec newRow *
          star ((preparation width).normalized.vec newColumn)) *
            state.quantumMarginal.matrix oldRow oldColumn :=
  Circuit.prepareZero_joined_entry (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty) state controlKey (controlLayout width)
    (control_fresh width) (control_disjoint width)
    newRow newColumn oldRow oldColumn

private theorem preparation_vec (width : Nat) (basis : (controlLayout width).register.Index) :
    (preparation width).normalized.vec basis =
      if basis = (preparation width).value then 1 else 0 :=
  NormalizedVector.ket_apply _ _

/-- On the prepared zero coordinate, the actual full matrix is exactly the old joint matrix. -/
theorem execute_zero_entry (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (oldRow oldColumn : (Register.prod (before width).register Reference).Index) :
    ((circuit width).execute Reference state).quantumMarginal.matrix
      (joined width (preparation width).value oldRow)
      (joined width (preparation width).value oldColumn) =
        state.quantumMarginal.matrix oldRow oldColumn := by
  rw [execute_joined_entry]
  simp only [preparation_vec, ↓reduceIte, star_one, one_mul]

/-- No actual matrix row has nonzero support when the fresh Ctrl value is nonzero. -/
theorem execute_nonzero_control_row (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (newRow newColumn : (controlLayout width).register.Index)
    (oldRow oldColumn : (Register.prod (before width).register Reference).Index)
    (nonzero : newRow 0 ≠ 0) :
    ((circuit width).execute Reference state).quantumMarginal.matrix
      (joined width newRow oldRow) (joined width newColumn oldColumn) = 0 := by
  have different : newRow ≠ (preparation width).value := by
    intro same
    apply nonzero
    exact (congrArg (fun basis : (controlLayout width).register.Index => basis 0) same).trans
      (prepared_control_zero width)
  rw [execute_joined_entry, preparation_vec, if_neg different, zero_mul, zero_mul]

/-- Neither off-diagonal column support nor any reference coherence can hide a nonzero Ctrl. -/
theorem execute_nonzero_control_column (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (newRow newColumn : (controlLayout width).register.Index)
    (oldRow oldColumn : (Register.prod (before width).register Reference).Index)
    (nonzero : newColumn 0 ≠ 0) :
    ((circuit width).execute Reference state).quantumMarginal.matrix
      (joined width newRow oldRow) (joined width newColumn oldColumn) = 0 := by
  have different : newColumn ≠ (preparation width).value := by
    intro same
    apply nonzero
    exact (congrArg (fun basis : (controlLayout width).register.Index => basis 0) same).trans
      (prepared_control_zero width)
  rw [execute_joined_entry, preparation_vec width newColumn, if_neg different, star_zero,
    mul_zero, zero_mul]

/-- The complete external-reference matrix is unchanged by the actual preparation instruction. -/
theorem execute_reference_entry (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H))
    (left right : Reference.Index) :
    (∑ basis : (after width).register.Index,
      ((circuit width).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before width).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) :=
  Circuit.prepareZero_reference_entry (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty) state controlKey (controlLayout width)
    (control_fresh width) (control_disjoint width) left right

theorem execute_mass (width : Nat)
    (state : State (before width) Reference (ClassicalOracleModel.empty.HiddenState × H)) :
    ((circuit width).execute Reference state).mass = state.mass :=
  Circuit.execute_mass (circuit width) Reference state

end

end QuantumAlg.MAU.Inversion.SharedEEA.ControlPreparation
