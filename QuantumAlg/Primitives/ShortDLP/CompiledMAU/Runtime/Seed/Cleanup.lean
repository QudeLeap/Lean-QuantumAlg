/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Restart
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Resources
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation

/-!
# Physical restart of the actual short-DLP bank

Every path through a nonempty reset bank contains a real Z measurement, including
paths selecting the identity correction. The subsequent literal X reload leaves
one predetermined seed in every complete execution record. On the owned-bank
interface, the actual execution also restores the borrowed classical/reference view.

The positive width condition excludes only an empty physical bank. It does not
restrict the modulus, initial quantum state, reference, history or path. In the
EH specialization the first exponent width is already positive. These cleanup
certificates do not assert completion of an independent caller cycle protocol.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma scopedReset_measured {bank : RuntimeCtx .quantum}
    (qubits : ∀ wire : Fin bank.systemCount,
      (bank.quantumLayout.wire wire).dimension = 2)
    (positive : 0 < bank.systemCount)
    (path : (ZReset.BankParallel.code (oracles := .empty) qubits BitWord.model).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := model) dimension ∈
      (ZReset.BankParallel.code (oracles := .empty) qubits BitWord.model).eventTrace path :=
  ⟨2, ZReset.BankParallel.code_measured qubits positive path⟩

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

include sameWires in
/-- The independent complete register width supplies an actual physical wire. -/
lemma shortDLP_runtimeBank_nonempty (positive : 0 < m + 2 * ell + 2 * width) :
    0 < ctx.systemCount := by
  have sourcePositive : 0 < totalQubits (registerParameters m ell width) := by
    rw [totalQubits_eq]
    exact positive
  have actual := (RuntimePlacement.wireEquiv m ell width sameWires
    ⟨0, sourcePositive⟩).isLt
  exact lt_of_le_of_lt (Nat.zero_le _) actual

/-- The bank reset contributes a real measurement on every reset/reload path. -/
lemma shortDLP_runtimeResetReload_measured (N : Nat)
    (positive : 0 < m + 2 * ell + 2 * width)
    (path : (resetReload m ell width sameWires N).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := model) dimension ∈
      (resetReload m ell width sameWires N).eventTrace path := by
  unfold resetReload at path ⊢
  obtain ⟨dimension, present⟩ := scopedReset_measured
    (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
    (shortDLP_runtimeBank_nonempty m ell width sameWires positive) path.1
  exact ⟨dimension, List.mem_append.mpr (Or.inl present)⟩

/-- Every complete round includes the actual nonempty bank reset measurement. -/
lemma shortDLP_runtimeRound_measured {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (positive : 0 < m + 2 * ell + 2 * width)
    (path : (code m ell width sameWires parameter N generator target cells result).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := model) dimension ∈
      (code m ell width sameWires parameter N generator target cells result).eventTrace path := by
  unfold code at path ⊢
  obtain ⟨dimension, present⟩ := shortDLP_runtimeResetReload_measured
    m ell width sameWires N positive path.2.2.2
  exact ⟨dimension, List.mem_append.mpr (Or.inr
    (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr present)))))⟩

-- Physical cleanup uses already proved trace, restoration and record-state facts.
-- Keep the actual circuit parameters opaque during their dependent assembly.
attribute [local irreducible] resetReload code

/-- Actual reset/reload meets physical cleanup with its predetermined, possibly nonzero seed. -/
lemma shortDLP_runtimeResetReload_restartCleanup (N : Nat)
    (positive : 0 < m + 2 * ell + 2 * width)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (environment := environment) (resetReload m ell width sameWires N) where
  measured := shortDLP_runtimeResetReload_measured m ell width sameWires N positive
  restores := by
    intro Reference History _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment)
      (model := model) (pre := ctx) (post := ctx)
      (resetReload m ell width sameWires N) noBorrowed Reference (History := History) state
  reinitialized := by
    refine ⟨ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ
      ((RuntimePlacement.basisEquiv m ell width sameWires).symm
        (CompiledMAU.reloadLabel m ell width N)), ?_⟩
    intro Reference History _ state label
    exact shortDLP_runtimeResetReload_recordSeed m ell width sameWires N
      state label ctx.borrowedSelectionᶜ

/-- The actual selected/readout/pack/reset/reload round cleans the owned bank.
The caller must separately certify its fixed protocol and the continuation's actual entry. -/
lemma shortDLP_runtimeRound_restartCleanup {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (positive : 0 < m + 2 * ell + 2 * width)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (environment := environment)
      (code m ell width sameWires parameter N generator target cells result) where
  measured := shortDLP_runtimeRound_measured m ell width sameWires parameter N
    generator target cells result positive
  restores := by
    intro Reference History _ state
    exact shortDLP_runtimeRound_borrowedRestored m ell width sameWires parameter N
      generator target cells result noBorrowed state
  reinitialized := by
    refine ⟨ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ
      ((RuntimePlacement.basisEquiv m ell width sameWires).symm
        (CompiledMAU.reloadLabel m ell width N)), ?_⟩
    intro Reference History _ state label
    exact shortDLP_runtimeRound_recordSeed m ell width sameWires parameter N
      generator target cells result state label ctx.borrowedSelectionᶜ

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
