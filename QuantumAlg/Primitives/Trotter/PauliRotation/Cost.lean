/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.PauliRotation.Rotation
import all QuantumAlg.Primitives.Trotter.PauliRotation.Rotation
import all QuantumAlg.Primitives.Trotter.PauliRotation.Basis
import all QuantumAlg.Primitives.Trotter.PauliRotation.Parity
import all QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Native event accounting for Pauli rotations

The literal S/H basis changes and both parity passes determine the native
pool. No arbitrary rotation synthesis is included
[WBA11, h2.arxiv2.tex:384-412].
-/

namespace QuantumAlg.Trotter

/-- Number of occurrences of a specific Pauli letter. -/
@[expose] public def pauliLetterCount {n : ℕ} (P : PauliString n) (a : PauliLetter) : ℕ :=
  (Finset.univ.filter fun j => P j = a).card

namespace PauliRotation

noncomputable section

private lemma sum_letter {n : ℕ} (P : PauliString n) (a : PauliLetter)
    (v : ResourcePool (.quantum AlgorithmGate.model .empty)) :
    (∑ j, if P j = a then v else 0) = pauliLetterCount P a • v := by
  rw [← Finset.sum_filter]
  simp [pauliLetterCount]

private lemma basis_pair_cost (a : PauliLetter) :
    (basisIn a).eventCost + (basisOut a).eventCost =
      (if a = .x then 2 • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) else 0) +
      (if a = .y then 2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) +
        4 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) else 0) := by
  cases a <;>
    simp [basisIn, basisOut, idle, NativeCircuit.single_eventCost,
      UnitaryCircuit.seq_eventCost, UnitaryCircuit.iterate_eventCost,
      succ_nsmul]
  abel

lemma layers_eventCost {n : ℕ} (P : PauliString n) :
    (inputLayer P).eventCost + (outputLayer P).eventCost =
      (2 * (pauliLetterCount P .x + pauliLetterCount P .y)) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) +
      (4 * pauliLetterCount P .y) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) := by
  rw [inputLayer, outputLayer, tensorCircuit_eventCost, tensorCircuit_eventCost,
    ← Finset.sum_add_distrib]
  simp only [basis_pair_cost]
  rw [Finset.sum_add_distrib, sum_letter, sum_letter, nsmul_add, smul_smul, smul_smul,
    smul_smul, ← add_assoc, ← add_nsmul]
  congr 1 <;> congr 1 <;> omega

lemma central_eventCost {n : ℕ} (P : PauliString n) (t : Fin n)
    (ht : t ∈ P.support) (θ : ℝ) :
    (central P t θ).eventCost =
      (2 * (P.weight - 1)) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit) := by
  simp only [central, UnitaryCircuit.seq_eventCost, NativeCircuit.inverse_eventCost,
    parity_eventCost, controls_length P t ht, rotationAt_eventCost]
  rw [two_mul, add_nsmul]
  abel

end
end PauliRotation
end QuantumAlg.Trotter
