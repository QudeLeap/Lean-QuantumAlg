/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Admission
import all QuantumAlg.Core.Execution.Basis.Seeded.Record.Cleanup
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# Actual complete Shor round boundaries

Each admitted cycle solves the independent complete protocol. Its actual
reset measures the same physical bank and establishes one fixed pure owned
seed on every complete store, service, history and path record. The next
protocol is admitted by the genuine predecessor, without reinitializing its
classical store or service state.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round

open Execution

noncomputable section

/-- The fixed zero label is chosen independently of every execution outcome. -/
def zeroSeed (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Iteration.context ctx N).quantumLayout.SelectedBasis
      (Iteration.context ctx N).borrowedSelectionᶜ :=
  (Iteration.context ctx N).quantumLayout.restrictSelectedBasis
    (Iteration.context ctx N).borrowedSelectionᶜ (Iteration.context ctx N).quantumLayout.zeroLabel

/-- Actual complete reset establishes that seed even on zero-mass complete records. -/
theorem reinitializedAt (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (Completion.code ctx N input sameWires cells result)
      (zeroSeed ctx N) := by
  exact BasisSeeded.reinitializedAt_of_holds
    (Completion.code ctx N input sameWires cells result)
    (Iteration.context ctx N).quantumLayout.zeroLabel
    (fun Reference {_} _ state => Completion.code_seeded ctx N input sameWires cells result state)
    ((Completion.code ctx N input sameWires cells result).borrowedQuantumWires_preserved.trans
      noBorrowedQuantum)

/-- Every actual complete path includes the physical reset's genuine measurement. -/
theorem measured (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (path : (Completion.code ctx N input sameWires cells result).Path) :
    ∃ dimension : (executionModel input).SystemDimension,
      Resource.Event.measurement dimension ∈
        (Completion.code ctx N input sameWires cells result).eventTrace path := by
  rcases path with ⟨iterationPath, recoveryPath, resetPath⟩
  have positive : 0 < (Iteration.context ctx N).systemCount := by
    rw [reset_bank_systemCount (Iteration.context ctx N) N
      ((Iteration.quantumWires ctx N).trans sameWires), bankQubits_eq_three_mul]
    exact Nat.mul_pos (by norm_num) input.modulusBits_pos
  obtain ⟨dimension, present⟩ := ZReset.BankScope.zResetBankScope_measured
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (shorDeclared_context_qubits N ((Iteration.quantumWires ctx N).trans sameWires))
    BitWord.model positive resetPath
  exact ⟨dimension, List.mem_append.mpr
    (Or.inr (List.mem_append.mpr (Or.inr present)))⟩

/-- Full restoration and fixed-record physical restart belong to the actual completed body. -/
theorem restartCleanup (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (noBorrowedQuantum : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (Completion.code ctx N input sameWires cells result) := by
  refine ⟨measured ctx N input sameWires cells result, ?_, ⟨zeroSeed ctx N,
    reinitializedAt ctx N input sameWires cells result noBorrowedQuantum⟩⟩
  intro Reference History _ state
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (Completion.code ctx N input sameWires cells result) noBorrowedQuantum Reference state

/-- A cycle certificate includes the independent protocol and every actual Solves obligation. -/
def completeCycle (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result)
    (noBorrowedQuantum : ctx.borrowedQuantumWires = [])
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CompleteCycle
      (Completion.code ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells result)
      (problem ctx model cells duration unitQueries) where
  output := (algorithm ctx model sameWires cells result).run.output
  certified := shorDeclared_round_solves ctx model sameWires cells result separated
    noBorrowedQuantum duration unitQueries

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round
