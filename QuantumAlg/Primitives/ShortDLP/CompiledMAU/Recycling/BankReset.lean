/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Program
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Resources
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Semantics
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Observation
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Actual complete reset of the one-control arithmetic bank

The existing parallel bank reset
allocates one real binary workspace cell per physical wire, measures every
wire, applies the stored-result-selected native correction layer, then exits
only those fresh scopes. The same actual code preserves every original
store/reference block. It neither reuses nor overwrites the retained member
output cells. Reload and complete retry composition remain separate work.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.BankReset

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Every actual wire belongs to the one-control qubit layout, including both arithmetic words. -/
lemma allQubits (wire : Fin (Context base noQuantum m ell width).systemCount) :
    ((Context base noQuantum m ell width).quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨source, rfl⟩ := (positionsOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width)).surjective wire
  exact (congrArg QuantumWire.dimension (wireAtCorrespondingPosition
    (Arithmetic.layout width).toQuantum (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) source)).trans (by rfl)

/-- The actual parent scopes supply all simultaneous reset outcomes and release them afterward. -/
def code : Circuit model (Context base noQuantum m ell width)
    (Context base noQuantum m ell width) :=
  ZReset.BankParallel.code (oracles := .empty) (allQubits base noQuantum m ell width)
    BitWord.model .empty

/-- Independent native envelope for the real bank, with every Z write and possible correction. -/
def eventBudget : ResourcePool model :=
  (1 + 2 * width) • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) +
    (1 + 2 * width) • ResourcePool.singleton (model := model) (.gate .singleQubit)

/-- The actual reset measures all 1+2w physical wires exactly once. -/
lemma recyclingBankReset_measurement_count
    (path : (code base noQuantum m ell width).Path) :
    ResourcePool.count (model := model) (.measurement (2 : ℕ+))
      ((code base noQuantum m ell width).resourcePool path) = 1 + 2 * width :=
  (ZReset.BankParallel.code_measurement_count (allQubits base noQuantum m ell width)
    path).trans (systemCount_eq base noQuantum m ell width)

/-- The same complete execution obeys the parameter-only native event envelope. -/
lemma recyclingBankReset_events (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).resourcePool path ≤ eventBudget width := by
  simpa only [eventBudget, systemCount_eq, code] using
    ZReset.BankParallel.code_resourcePool_le (allQubits base noQuantum m ell width) path

/-- Every actual path has at most one quantum correction layer, including all measurements. -/
lemma recyclingBankReset_quantumTime (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).quantumTime path ≤ 1 :=
  ZReset.BankParallel.code_quantumTime_le (allQubits base noQuantum m ell width) path

/-- Resident peak includes the exact fresh reset bits, retained results and original context. -/
lemma recyclingBankReset_resident (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).peakResidentSpace path =
      ((1 + 2 * width) + resultBits m ell) • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.residentSpace) := by
  calc
    _ = (Context base noQuantum m ell width).systemCount • SpacePool.ofShape (.finite 2) +
        (Context base noQuantum m ell width).residentSpace :=
      ZReset.BankParallel.code_peakResidentSpace (allQubits base noQuantum m ell width) path
    _ = _ := by
      rw [systemCount_eq, context_resident]
      simp only [add_nsmul]
      ac_rfl

/-- Auxiliary peak charges the same actual reset scratch and every live retained result bit. -/
lemma recyclingBankReset_auxiliary (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).peakAuxiliarySpace path =
      ((1 + 2 * width) + resultBits m ell) • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout (Arithmetic.layout width).toQuantum + base.auxiliarySpace) := by
  calc
    _ = (Context base noQuantum m ell width).systemCount • SpacePool.ofShape (.finite 2) +
        (Context base noQuantum m ell width).auxiliarySpace :=
      ZReset.BankParallel.code_peakAuxiliarySpace (allQubits base noQuantum m ell width) path
    _ = _ := by
      rw [systemCount_eq, context_auxiliary]
      simp only [add_nsmul]
      ac_rfl

/-- The actual reset internally establishes the zero bank for arbitrary incoming mixed states. -/
lemma recyclingBankReset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (Context base noQuantum m ell width).quantumLayout.zeroLabel
      ((code base noQuantum m ell width).execute environment Reference state) :=
  ZReset.BankParallel.seeded (allQubits base noQuantum m ell width) state

/-- Every complete original store retains its entire reference block at the zero physical bank. -/
lemma recyclingBankReset_store_entry
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (original : Store (Context base noQuantum m ell width))
    (left right : (Context base noQuantum m ell width).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((code base noQuantum m ell width).execute environment Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = (Context base noQuantum m ell width).quantumLayout.zeroLabel ∧
          right = (Context base noQuantum m ell width).quantumLayout.zeroLabel then
        ∑ basis : (Context base noQuantum m ell width).register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 :=
  ZReset.BankParallel.code_complete_store_entry
    (allQubits base noQuantum m ell width) state original left right leftRef rightRef

/-- No previous output, borrowed classical value or its reference correlation is overwritten. -/
lemma recyclingBankReset_referenceFiberSum
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (weight : Store (Context base noQuantum m ell width) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width).execute environment Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
        ExecutionState.referenceFiberSum state
          (fun entry _ => weight entry.1) leftRef rightRef :=
  ZReset.BankParallel.referenceFiberSum_preserved
    (allQubits base noQuantum m ell width) state weight leftRef rightRef

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.BankReset
