/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.DynamicalLieAlgebra
public import QuantumAlg.Primitives.QNN.AdModule
public import QuantumAlg.Primitives.QNN.Overparametrization
public import QuantumAlg.Primitives.QNN.Trainability
public import QuantumAlg.Primitives.QNN.LieAlgebraicBP
public import QuantumAlg.Primitives.QNN.VarianceFormula
public import QuantumAlg.Primitives.QNN.FullDLABasis
public import QuantumAlg.Primitives.QNN.SimpleDLA
public import QuantumAlg.Primitives.QNN.PauliStringDLA
public import QuantumAlg.Primitives.QNN.OrthogonalDLA
public import QuantumAlg.Primitives.QNN.SymplecticDLA
public import QuantumAlg.Primitives.QNN.PauliPropagation
public import QuantumAlg.Primitives.QNN.SingleQubitDLA
public import QuantumAlg.Primitives.QNN.QuantumFisherRank
public import QuantumAlg.Primitives.QNN.OverparametrizationDef

/-!
# Quantum neural networks: dynamical Lie algebras and trainability

Umbrella module for the quantum-neural-network and barren-plateau development.

- `QNN.DynamicalLieAlgebra` — the dynamical Lie algebra of a generator set.
- `QNN.Overparametrization` — overparametrization capacity bound.
- `QNN.Trainability` — exponential-concentration / barren-plateau foundations.
- `QNN.LieAlgebraicBP` — the DLA-dimension → variance → barren-plateau chain.
- `QNN.VarianceFormula` — the Ragone reductive variance formula.
- `QNN.FullDLABasis` — the explicit `gl(2ⁿ)` Hermitian basis and concrete exponential BP.
- `QNN.SimpleDLA` — the genuine `su(2)` algebra; the `g ≃ su(d)` single-ideal
  variance and barren plateau.
- `QNN.PauliStringDLA` — the `n`-qubit Pauli-string basis of `su(2ⁿ)` for all
  `n`; concrete McClean barren plateau.
- `QNN.OrthogonalDLA` — the odd-`#Y` Pauli realization of `so(2ⁿ)`;
  single-ideal variance and exponential barren plateau.
- `QNN.SymplecticDLA` — the `θ=+1` Pauli realization of `sp(2ⁿ)`;
  single-ideal variance and exponential barren plateau.
- `QNN.PauliPropagation` — Pauli-propagation truncation error.
- `QNN.SingleQubitDLA` — locality-induced no-barren-plateau for `su(2)^{⊕n}`
  (local observable, `Var = 1/3`).
- `QNN.QuantumFisherRank` — the QFIM-rank bound `rank[F] ≤ dim g`
  (Larocca Theorem 1), proved from the DLA real-form structure.
- `QNN.OverparametrizationDef` — the QFIM-rank-saturation
  overparametrization predicate `R(M) = R` (Larocca Def. 1) + critical count
  `M_c`.
-/

@[expose] public section
