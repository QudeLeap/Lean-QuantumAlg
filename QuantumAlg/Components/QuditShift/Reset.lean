/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift
import all QuantumAlg.Core.Measure.Reset

/-!
# One-wire Z measurement and its selected cyclic correction

After a Z result is stored, selecting the shift by its additive inverse resets
that physical system to zero. All matrix indices of the other systems remain
present, so their complete joint conditional state is retained. The formulas
apply to arbitrary heterogeneous layouts and arbitrary joint inputs.

These internal state-update proofs instantiate the local measurement rule
[dW19, qcnotes.tex:5420] followed by unitary conjugation
[dW19, qcnotes.tex:5405]. The execution syntax remains responsible for writing
and reading the classical result and recording the measurement and gate events.
-/

section

namespace QuantumAlg.QuditShift

noncomputable section

variable {systemCount : Nat}

private instance resetDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- Entrywise effect of the concrete shift on the complete stored quantum state. -/
lemma operator_density_entry (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (ρ : DensityOperator layout.register)
    (left right : layout.Basis) :
    (DensityOperator.applyUnitary (operator layout wire amount) ρ).matrix left right =
      ρ.matrix (Function.update left wire (left wire - amount))
        (Function.update right wire (right wire - amount)) := by
  exact ZReset.permutationDensityEntry (R := layout.register)
    (labelShift layout wire amount).symm ρ left right

/-- The quantum branch after measuring this wire and selecting its negative-result shift. -/
def resetBranch (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (outcome : Fin (layout.wire wire).dimension) (ρ : DensityOperator layout.register) :
    DensityOperator layout.register :=
  DensityOperator.applyUnitary (operator layout wire (-outcome))
    (ZMeasurement.branch (R := layout.register)
      (fun basis : layout.Basis => basis wire) outcome ρ)

/-- Each actual branch has zero on the measured wire and preserves the full
conditional matrix block of every other wire, with no separability assumption. -/
lemma resetBranch_entry (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (outcome : Fin (layout.wire wire).dimension) (ρ : DensityOperator layout.register)
    (left right : layout.Basis) :
    (resetBranch layout wire outcome ρ).matrix left right =
      if left wire = 0 ∧ right wire = 0 then
        ρ.matrix (Function.update left wire outcome) (Function.update right wire outcome)
      else 0 := by
  rw [resetBranch, operator_density_entry]
  refine (ZMeasurement.branch_matrix (R := layout.register)
    (fun basis : layout.Basis => basis wire) outcome ρ
    (Function.update left wire (left wire - -outcome))
    (Function.update right wire (right wire - -outcome))).trans ?_
  simp only [Function.update_self, sub_neg_eq_add, ZReset.shiftedLabelEqOutcome]
  by_cases hl : left wire = 0 <;> by_cases hr : right wire = 0 <;> simp [hl, hr]

/-- The correction leaves the probability of the actual Z result unchanged. -/
lemma resetBranch_mass (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (outcome : Fin (layout.wire wire).dimension) (ρ : DensityOperator layout.register) :
    (resetBranch layout wire outcome ρ).mass =
      (ZMeasurement.branch (R := layout.register)
        (fun basis : layout.Basis => basis wire) outcome ρ).mass := by
  exact DensityOperator.applyUnitary_mass (R := layout.register) _ _

/-- Summing all recorded outcomes gives zero on the selected wire and the
original joint marginal of all other systems, including their coherences. -/
lemma resetSum_entry (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (ρ : DensityOperator layout.register) (left right : layout.Basis) :
    (∑ outcome, (resetBranch layout wire outcome ρ).matrix) left right =
      if left wire = 0 ∧ right wire = 0 then
        ∑ outcome, ρ.matrix (Function.update left wire outcome)
          (Function.update right wire outcome)
      else 0 := by
  calc
    _ = ∑ outcome, (resetBranch layout wire outcome ρ).matrix left right :=
      Matrix.sum_apply left right Finset.univ _
    _ = _ := by
      simp only [resetBranch_entry]
      by_cases h : left wire = 0 ∧ right wire = 0 <;> simp [h]

/-- The complete measurement-and-correction sequence preserves total mass. -/
lemma resetSum_mass (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (ρ : DensityOperator layout.register) :
    ∑ outcome, (resetBranch layout wire outcome ρ).mass = ρ.mass := by
  simp only [resetBranch_mass]
  exact ZMeasurement.sum_branch_mass (R := layout.register)
    (fun basis : layout.Basis => basis wire) ρ

end

end QuantumAlg.QuditShift

end
