/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Placement
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Observation
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Bounds

/-!
# Paid physical reset of the same declared Shor bank

The parallel measurement-and-X sequence uses one actual lexical cell per wire.
It neither prepares nor replaces a quantum system. Every complete original
store-reference block survives, while the unchanged bank becomes zero.
Restoration of borrowed quantum systems requires a separate ownership proof.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Exact extra capacity of the simultaneously allocated classical result bank. -/
def resetSpace (N : Nat) : SpacePool .quantum :=
  bankQubits N • SpacePool.ofShape (.finite 2)

variable (ctx : RuntimeCtx .quantum) (N : Nat)
  (sameWires : ctx.quantumWires = (layout N).wires)

variable {environment : (executionModel N).Environment}

/-- Reset the original physical bank with one real scoped result cell per wire. -/
def reset : Circuit (executionModel N) ctx ctx :=
  ZReset.BankParallel.code (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) BitWord.model

include sameWires in
/-- Actual corresponding wire positions determine the complete physical width. -/
lemma reset_bank_systemCount : ctx.systemCount = bankQubits N := by
  have same := Fintype.card_congr (wireEquiv N sameWires)
  simpa only [Fintype.card_fin] using same.symm

/-- The actual reset establishes zero on each complete original store-reference block. -/
lemma reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History)) :
    BasisSeeded.Holds ctx.quantumLayout.zeroLabel
      ((reset ctx N sameWires).execute environment Reference state) := by
  exact ZReset.BankParallel.seeded (services := .empty) (operations := BitWord.model)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) state

/-- Reset preserves every weight of the complete original store and arbitrary reference. -/
lemma reset_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel N).HiddenState × History))
    (weight : Store ctx → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reset ctx N sameWires).execute environment Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight entry.1) leftRef rightRef :=
  ZReset.BankParallel.referenceFiberSum_preserved
    (services := .empty) (operations := BitWord.model)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) state weight leftRef rightRef

/-- Each actual path pays one measurement and at most one native X per bank wire. -/
lemma reset_events_le (path : (reset ctx N sameWires).Path) :
    (reset ctx N sameWires).resourcePool path ≤
      ZReset.Bank.envelope
        (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
        (bankQubits N) BitWord.model := by
  have paid := ZReset.BankParallel.code_eventEnvelope_le (services := .empty)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at paid
  exact paid

/-- Total native work bounds the same reset depth by twice the complete bank width. -/
lemma reset_depth_le (path : (reset ctx N sameWires).Path) :
    (reset ctx N sameWires).depth (fun _ => 1) path ≤ 2 * bankQubits N := by
  have paid := ZReset.BankParallel.code_unitDepth_le (services := .empty)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at paid
  exact paid

/-- Canonical time counts one simultaneous correction layer, or zero for an empty bank. -/
lemma reset_quantumTime_le (path : (reset ctx N sameWires).Path) :
    (reset ctx N sameWires).quantumTime path ≤ if bankQubits N = 0 then 0 else 1 := by
  have bounded := ZReset.BankParallel.code_quantumTime_le_layer (services := .empty)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at bounded
  exact bounded

/-- The actual resident peak includes every real simultaneously allocated result cell. -/
lemma reset_peakResidentSpace (path : (reset ctx N sameWires).Path) :
    (reset ctx N sameWires).peakResidentSpace path =
      resetSpace N + ctx.residentSpace := by
  have peak := ZReset.BankParallel.code_peakResidentSpace (services := .empty)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at peak
  exact peak

/-- The same result group is charged in full to the actual auxiliary peak. -/
lemma reset_peakAuxiliarySpace (path : (reset ctx N sameWires).Path) :
    (reset ctx N sameWires).peakAuxiliarySpace path =
      resetSpace N + ctx.auxiliarySpace := by
  have peak := ZReset.BankParallel.code_peakAuxiliarySpace (services := .empty)
    (oracles := DeclaredSource.model (modulusBits N) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at peak
  exact peak

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
