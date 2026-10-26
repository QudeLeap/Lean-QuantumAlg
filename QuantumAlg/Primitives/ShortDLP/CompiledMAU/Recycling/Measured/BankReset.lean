/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Context
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Program
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Resources
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Semantics
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Observation
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Base.Layout.Qubit

/-!
# Actual complete measured-frame reset with parent-owned scalar scratch

The existing parallel bank reset
allocates one real binary workspace cell per physical wire, measures every
wire, applies the stored-result-selected native correction layer, then exits
only those fresh scopes. The same actual code preserves every original
store/reference block. It neither reuses nor overwrites the retained member
output cells. Reload and complete retry composition remain separate work.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.BankReset

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Every original wire is a qubit, including both words, both helpers and the flag. -/
lemma measuredBankReset_allQubits (wire : Fin (Context base noQuantum m ell width).systemCount) :
    ((Context base noQuantum m ell width).quantumLayout.wire wire).dimension = 2 := by
  obtain ⟨source, rfl⟩ := (positionsOfEqualWires (Physical.qubits width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width)).surjective wire
  exact (congrArg QuantumWire.dimension (wireAtCorrespondingPosition
    (Physical.qubits width).toQuantum (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) source)).trans (by rfl)

/-- The actual parent scopes supply all simultaneous reset outcomes and release them afterward. -/
def code : Circuit model (Context base noQuantum m ell width)
    (Context base noQuantum m ell width) :=
  ZReset.BankParallel.code (oracles := .empty)
    (measuredBankReset_allQubits base noQuantum m ell width)
    BitWord.model .empty

/-- Independent native envelope for the real bank, with every Z write and possible correction. -/
def eventBudget : ResourcePool model :=
  (2 * width + 4) • ResourcePool.singleton (model := model) (.measurement (2 : ℕ+)) +
    (2 * width + 4) • ResourcePool.singleton (model := model) (.gate .singleQubit)

/-- The actual reset measures all 2w+4 physical wires exactly once. -/
lemma measuredBankReset_measurement_count
    (path : (code base noQuantum m ell width).Path) :
    ResourcePool.count (model := model) (.measurement (2 : ℕ+))
      ((code base noQuantum m ell width).resourcePool path) = 2 * width + 4 :=
  (ZReset.BankParallel.code_measurement_count
    (measuredBankReset_allQubits base noQuantum m ell width)
    path).trans (systemCount_eq base noQuantum m ell width)

/-- The same complete execution obeys the parameter-only native event envelope. -/
lemma measuredBankReset_events (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).resourcePool path ≤ eventBudget width := by
  simpa only [eventBudget, systemCount_eq, code] using
    ZReset.BankParallel.code_resourcePool_le
      (measuredBankReset_allQubits base noQuantum m ell width) path

/-- Every actual path has at most one quantum correction layer, including all measurements. -/
lemma measuredBankReset_quantumTime (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).quantumTime path ≤ 1 :=
  ZReset.BankParallel.code_quantumTime_le
    (measuredBankReset_allQubits base noQuantum m ell width) path

/-- Every fresh physical reset result cell is included in the actual resident peak. -/
lemma measuredBankReset_resident (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).peakResidentSpace path =
      (2 * width + 4) • SpacePool.ofShape (.finite 2) +
        (Context base noQuantum m ell width).residentSpace := by
  exact (ZReset.BankParallel.code_peakResidentSpace
    (measuredBankReset_allQubits base noQuantum m ell width) path).trans
      (congrArg (fun count : Nat => count • SpacePool.ofShape (.finite 2) +
        (Context base noQuantum m ell width).residentSpace)
          (systemCount_eq base noQuantum m ell width))

/-- Every fresh scalar scratch cell is also charged at the actual auxiliary peak. -/
lemma measuredBankReset_auxiliary (path : (code base noQuantum m ell width).Path) :
    (code base noQuantum m ell width).peakAuxiliarySpace path =
      (2 * width + 4) • SpacePool.ofShape (.finite 2) +
        (Context base noQuantum m ell width).auxiliarySpace := by
  exact (ZReset.BankParallel.code_peakAuxiliarySpace
    (measuredBankReset_allQubits base noQuantum m ell width) path).trans
      (congrArg (fun count : Nat => count • SpacePool.ofShape (.finite 2) +
        (Context base noQuantum m ell width).auxiliarySpace)
          (systemCount_eq base noQuantum m ell width))

/-- The actual reset internally establishes the zero bank for arbitrary incoming mixed states. -/
lemma measuredBankReset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History)) :
    BasisSeeded.Holds (Context base noQuantum m ell width).quantumLayout.zeroLabel
      ((code base noQuantum m ell width).execute environment Reference state) :=
  ZReset.BankParallel.seeded
    (measuredBankReset_allQubits base noQuantum m ell width) state

/-- Every complete original store retains its entire reference block at the zero physical bank. -/
lemma measuredBankReset_store_entry
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
    (measuredBankReset_allQubits base noQuantum m ell width) state original left right leftRef
      rightRef

/-- No previous output, borrowed classical value or its reference correlation is overwritten. -/
lemma measuredBankReset_referenceFiberSum
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
    (measuredBankReset_allQubits base noQuantum m ell width) state weight leftRef rightRef

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.BankReset
