/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.PauliRotation.Construction
import all QuantumAlg.Primitives.Trotter.PauliRotation.Construction
public import QuantumAlg.Components.Gates.GlobalPhase
import all QuantumAlg.Components.Gates.GlobalPhase
public import QuantumAlg.Components.Pauli.Groups
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Oracle.TimeEvolution
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Exact weighted Pauli terms

Nonempty strings use the native parity rotation [WBA11, h2.arxiv2.tex:384-412].
Identity strings instead retain their scalar phase as one named native gate.
Zero coefficients and zero angles retain the same literal leaves.
-/

section

namespace QuantumAlg.Trotter

noncomputable section

/-- Native exact circuit of one weighted term, retaining identity-term phases. -/
public def termCircuit {n : ℕ} [NeZero n] (a : ℝ × PauliString n) (τ : ℝ) : NativeCircuit n :=
  expPauli a.2 (a.1 * τ)

/-- Moving a real coefficient into evolution time preserves the exact operator. -/
public lemma termHamiltonian_evolution {n : ℕ} (a : ℝ × PauliString n) (τ : ℝ) :
    timeEvolution (PauliSum.termHamiltonian a) τ = timeEvolution a.2.hamiltonian (a.1 * τ) := by
  apply Subtype.ext
  change NormedSpace.exp (_ • ((a.1 : ℂ) • _)) = NormedSpace.exp (_ • _)
  rw [smul_smul]
  congr 2
  push_cast
  ring

/-- Exact term evolution, including every empty-support phase on positive-width registers. -/
public lemma termCircuit_matrix {n : ℕ} [NeZero n] (a : ℝ × PauliString n) (τ : ℝ) :
    (termCircuit a τ).binaryOperator = timeEvolution (PauliSum.termHamiltonian a) τ := by
  rw [termCircuit, expPauli_matrix, termHamiltonian_evolution]

/-- Input-only native pool for one weighted term. -/
@[expose] public def termPool {n : ℕ} (a : ℝ × PauliString n) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  if a.2.support.Nonempty then
    (2 * (a.2.weight - 1)) • {.gate .cnot} +
    {.gate .singleQubit} +
    (2 * (pauliLetterCount a.2 .x + pauliLetterCount a.2 .y)) •
      {.gate .singleQubit} +
    (4 * pauliLetterCount a.2 .y) • {.gate .singleQubit}
  else {.gate .singleQubit}

/-- Literal native resources do not depend on the coefficient or evolution time. -/
public lemma termCircuit_eventCost {n : ℕ} [NeZero n] (a : ℝ × PauliString n) (τ : ℝ) :
    (termCircuit a τ).eventCost = termPool a := by
  exact expPauli_eventCost a.2 (a.1 * τ)

end
end QuantumAlg.Trotter

end
