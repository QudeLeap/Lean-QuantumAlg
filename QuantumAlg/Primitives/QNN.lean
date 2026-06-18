/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.DynamicalLieAlgebra
public import QuantumAlg.Primitives.QNN.Overparametrization
public import QuantumAlg.Primitives.QNN.Trainability
public import QuantumAlg.Primitives.QNN.LieAlgebraicBP
public import QuantumAlg.Primitives.QNN.VarianceFormula
public import QuantumAlg.Primitives.QNN.FullDLABasis
public import QuantumAlg.Primitives.QNN.PauliPropagation

/-!
# Quantum neural networks: dynamical Lie algebras and trainability

Umbrella module for the quantum-neural-network and barren-plateau development.

- `QNN.DynamicalLieAlgebra` — the dynamical Lie algebra of a generator set.
- `QNN.Overparametrization` — overparametrization capacity bound.
- `QNN.Trainability` — exponential-concentration / barren-plateau foundations.
- `QNN.LieAlgebraicBP` — the DLA-dimension → variance → barren-plateau chain.
- `QNN.VarianceFormula` — the Ragone reductive variance formula.
- `QNN.FullDLABasis` — the explicit `su(2ⁿ)` Hermitian basis and concrete exponential BP.
- `QNN.PauliPropagation` — Pauli-propagation truncation error.
-/

@[expose] public section
