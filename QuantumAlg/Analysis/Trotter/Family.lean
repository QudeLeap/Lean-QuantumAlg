/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base.Hamiltonian
public import QuantumAlg.Components.Oracle.TimeEvolution

/-!
# Ordered Hamiltonian families and first-order products

The first-order product formula replaces evolution under a sum by an ordered
product of short-time evolutions [Lin22, trotter.tex:20-28]. Finite families use
increasing index order in the matrix product [CMN+18, simalg.tex:21].
These are operator definitions; no implemented circuit or resource claim is made.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator

noncomputable section

/-- A finite ordered family of Hamiltonian terms on a common register. -/
abbrev HamiltonianFamily (R : Register) (L : ℕ) : Type :=
  Fin L → Hamiltonian R

/-- Pairwise commutation of all Hamiltonian terms in a finite family. -/
def PairwiseCommute {R : Register} {L : ℕ} (terms : HamiltonianFamily R L) : Prop :=
  ∀ i j : Fin L, Commute (terms i : HilbertOperator R) (terms j : HilbertOperator R)

/-- One first-order product step, with its unconditional unitarity in the carrier. -/
def finiteFirstOrderTrotterStep {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (dt : ℝ) : UnitaryOperator R :=
  (List.ofFn fun j : Fin L => timeEvolution (terms j) dt).prod

@[simp]
lemma coe_finiteFirstOrderTrotterStep {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (dt : ℝ) :
    ((finiteFirstOrderTrotterStep terms dt : UnitaryOperator R) : HilbertOperator R) =
      (List.ofFn fun j : Fin L => timeEvolutionOp (terms j : HilbertOperator R) dt).prod := by
  simp [finiteFirstOrderTrotterStep, List.map_ofFn, Function.comp_def]

/-- Repeated finite-family product evolution as a certified unitary operator. -/
def finiteFirstOrderTrotterProduct {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (t : ℝ) (r : ℕ) : UnitaryOperator R :=
  (finiteFirstOrderTrotterStep terms (t / (r : ℝ))) ^ r

@[simp]
lemma coe_finiteFirstOrderTrotterProduct {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (t : ℝ) (r : ℕ) :
    ((finiteFirstOrderTrotterProduct terms t r : UnitaryOperator R) : HilbertOperator R) =
      ((finiteFirstOrderTrotterStep terms (t / (r : ℝ)) : UnitaryOperator R) :
        HilbertOperator R) ^ r := by
  simp [finiteFirstOrderTrotterProduct]

/-- One first-order Trotter step for two Hamiltonian summands, at the raw
operator level. -/
def firstOrderTrotterStepOp {R : Register} (H₁ H₂ : HilbertOperator R) (dt : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp H₁ dt * timeEvolutionOp H₂ dt

/-- A two-term first-order Trotter step is unitary when both summands are Hamiltonians. -/
lemma firstOrderTrotterStepOp_mem_unitaryGroup {R : Register}
    (H₁ H₂ : Hamiltonian R) (dt : ℝ) :
    firstOrderTrotterStepOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) dt
      ∈ Matrix.unitaryGroup R.Index ℂ := by
  unfold firstOrderTrotterStepOp
  exact mul_mem (timeEvolutionOp_mem_unitaryGroup H₁.2 dt)
    (timeEvolutionOp_mem_unitaryGroup H₂.2 dt)

/-- The repeated first-order Trotter product for two Hamiltonian summands. -/
def firstOrderTrotterProductOp {R : Register} (H₁ H₂ : HilbertOperator R)
    (t : ℝ) (r : ℕ) : HilbertOperator R :=
  (firstOrderTrotterStepOp H₁ H₂ (t / (r : ℝ))) ^ r

/-- The raw operator error of the two-term repeated first-order Trotter product. -/
def firstOrderTrotterErrorOp {R : Register} (H₁ H₂ : HilbertOperator R)
    (t : ℝ) (r : ℕ) : HilbertOperator R :=
  timeEvolutionOp (H₁ + H₂) t - firstOrderTrotterProductOp H₁ H₂ t r

end

end QuantumAlg
