/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Trainability
public import QuantumAlg.Primitives.QNN.Overparam
public import QuantumAlg.Primitives.QNN.Ansatz

/-!
# Quantum machine learning: trainability and expressivity

The public quantum-machine-learning surface has two pillars. This module is the
trainability umbrella for the quantum-neural-network and barren-plateau
development. The complementary expressivity pillar is
`QuantumAlg.Primitives.QNN.Expressivity`, which connects trigonometric
polynomials, QSP/QSVT, parameter-shift rules, quantum kernels, and QFIM capacity.

The trainability modules re-exported here are:

- `QNN.DynamicalLieAlgebra` — the dynamical Lie algebra of a generator set.
- `QNN.AdModule` — the restricted adjoint action, concrete `g ⊗ g` carrier,
  doubled commutant, and Hilbert-Schmidt projection infrastructure.
- `QNN.CasimirInvariant` — invariance of the quadratic Casimir under the
  doubled adjoint action.
- `QNN.RagoneInterface` — non-circular named hypotheses for the simple and
  reductive Ragone second-moment formulas.
- `QNN.DoubledTwirl` — the finite `t = 2` doubled twirl mechanism used to
  instantiate the second-moment interface.
- `QNN.SchurGeneric` — dimension-generic `(g⊗g)^g` infrastructure for Schur
  one-dimensionality discharges.
- `QNN.Overparametrization` — overparametrization capacity bound.
- `QNN.Trainability` — exponential-concentration / barren-plateau foundations.
- `QNN.TrainabilityWitnesses` — concrete adapters inhabiting the trainability interfaces.
- `QNN.LieAlgebraicBP` — the DLA-dimension → variance → barren-plateau chain.
- `QNN.VarianceFormula` — the Ragone reductive variance formula.
- `QNN.FullDLABasis` — the explicit `gl(2ⁿ)` Hermitian basis used by the QFIM-rank
  bound and the honest reductive `gl` treatment.
- `QNN.GlReductive` — the reductive `gl(2ⁿ) = su(2ⁿ) ⊕ center` variance law; no
  single-Casimir `gl` barren-plateau theorem is claimed.
- `QNN.SimpleDLA` — the genuine `su(2)` algebra and the simple-dimension
  single-ideal variance reduction.
- `QNN.PauliStringDLA` — the `n`-qubit Pauli-string basis of `su(2ⁿ)` for all
  `n`, plus the bundle-quantified variance and barren-plateau spine.
- `QNN.PauliAlgebra` — the Pauli-string product/commutator algebra and its symplectic structure
  (single-term brackets, non-degeneracy, anticommutation connectivity).
- `QNN.SchurSolver` — compatibility re-export for the old Pauli Schur-solver
  legacy module path.
- `QNN.PauliSchurFamily` — the shared Pauli-family Schur-discharge solver used
  by the `su`, `so`, and `sp` Pauli-string families.
- `QNN.PauliStringSchur` — the genuine Schur identity `(g⊗g)^g = span{C}` for `su(2ⁿ)` (all `n`),
  discharging hypothesis (H2); the Schur-discharged consistency witness.
- `QNN.OrthogonalDLA` — the odd-`#Y` Pauli realization of `so(2ⁿ)`; single-ideal variance and
  exponential barren plateau.
- `QNN.OrthogonalSchur` — the genuine Schur identity `(g⊗g)^g = span{C}` for the simple `so(2ᵐ)`
  (`m ≥ 3`), plus the one-dimensional `so(2)` case; the simple-family barren-plateau endpoint is the
  Schur-discharged consistency witness. (`so(4)` is a separate reductive special case.)
- `QNN.OrthogonalSO4` — the reductive special case `so(4) = su(2) ⊕ su(2)`: a generic Pauli-triangle
  `DLAHermBasis`, the genuine per-ideal Schur `(gⱼ⊗gⱼ)^gⱼ = span{Cⱼ}`, and the two-Casimir
  `RagoneReductive` variance (the single-Casimir Schur is false here).
- `QNN.OrthogonalSO4Schur` — the explicit `so(4)` negative-control theorem:
  the single-Casimir Schur identity is false and the invariant space has
  finrank `2`.
- `QNN.MatchgateSO` — the matchgate/free-fermion Majorana-quadratic `so(2n)`
  Pauli-family DLA: orthonormal Hermitian basis, closed-form `n(2n-1)`
  dimension, Schur discharge for `n ≥ 3`, the `so(4)` reductive exception, and
  the shifted polynomial-DLA consistency-witness dichotomy.
- `QNN.TFIM` — the Jordan--Wigner open-chain TFIM realization: physical
  `{iZ_j, iX_jX_{j+1}}` generators, their path-graph Lie closure, and the
  `n(2n-1)` Hermitian basis.
- `QNN.SymplecticDLA` — the `θ=+1` Pauli realization of `sp(2ⁿ)`; single-ideal variance and
  exponential barren plateau.
- `QNN.SymplecticSchur` — the genuine Schur identity `(g⊗g)^g = span{C}` for `sp(2ⁿ)` (all `n`),
  discharging hypothesis (H2); the Schur-discharged consistency witness.
- `QNN.PauliPropagation` — Pauli-propagation truncation error.
- `QNN.SingleQubitDLA` — locality-induced no-barren-plateau for `su(2)^{⊕n}` (local
  observable, `Var = 1/3`).
- `QNN.ProductClifford` — the `n`-fold product single-qubit Clifford doubled-twirl endpoint
  for the local family.
- `QNN.QuantumFisherRank` — the QFIM-rank bound `rank[F] ≤ dim g` (Larocca Theorem 1), proved from
  the DLA real-form structure.
- `QNN.QubitTwoDesign` — the strict `48`-element binary-octahedral lift and `24` projective
  single-qubit Clifford two-design.
- `QNN.OverparametrizationDef` — the QFIM-rank-saturation overparametrization predicate `R(M) = R`
  (Larocca Def. 1) + critical count `M_c`.
- `QNN.OverparamQFIM` — discharges the overparametrization `F` field with the genuine `qfim` on a
  real DLA generator family (`OverparamData.ofQFIM`); the `M_c` onset now rests on
  a real Fisher matrix.
- `QNN.Ansatz` — the multi-gate variational ansatz `U(θ) = ∏ₖ exp(-i(θₖ/2)Hₖ)`; the cost is *proved*
  frequency-1 trigonometric per coordinate, with the algebraic (derivative-free)
  parameter-shift rule.
- `QNN.GSim` — correctness of Lie-algebraic classical simulation: the Heisenberg observable stays in
  `g`, coordinates update by a `dim g × dim g` transfer matrix, the loss reconstructs from the
  `dim g` quantum data `Tr[ρ Bⱼ]`; capstone `gsim_variance_and_reconstruction`.
- `QNN.GSimLocal` — the local `su(2)^n` reconstruction witness using `3n`
  product-local data and the product single-qubit-Clifford doubled twirl.
- `QNN.PolyDLA` — the polynomial-size DLA schema: an inverse-polynomial
  variance floor rules out exponential concentration while exact g-sim data stay
  polynomial in the register size.
- `QNN.ClassicalDLAScaling` — weight-state purity and the conditional classical-family
  `sqrt(dim g) / 2^n` variance scaling.
- `QNN.TFIMWeightScaling` — the TFIM highest-weight endpoint with exact state
  and Setup-1 observable purities, inverse-linear second moment, and no barren plateau.
-/

@[expose] public section
