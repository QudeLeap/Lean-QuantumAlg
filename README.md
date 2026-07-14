# Lean-QuantumAlg

Lean-QuantumAlg is a Lean 4 library for formally verified quantum algorithms.

## What's Lean-QuantumAlg?

Lean-QuantumAlg provides reusable definitions, primitives, and theorem
statements for quantum algorithms in Lean. It is built on Mathlib and CSLib,
with public theorem endpoints organized so readers and agents can import the
modules they need.

### Aims

- Provide a modest, reusable Lean library for quantum-algorithm formalization.
- Keep algorithm statements tied to source references and stable import paths.
- Follow Mathlib and CSLib conventions closely enough to support later upstream
  review and reuse.

## Using Lean-QuantumAlg in your project

To add Lean-QuantumAlg as a dependency to a Lake project, add the following to
your `lakefile.toml`:

```toml
[[require]]
name = "QuantumAlg"
git = "https://github.com/QudeLeap/Lean-QuantumAlg.git"
rev = "main"
```

Use Lean `v4.30.0`. Then import either the aggregate module or a focused module:

```lean
import QuantumAlg
import QuantumAlg.Algorithms.Grover
import QuantumAlg.Algorithms.QPE
import QuantumAlg.Primitives.QFT
```

The library currently includes:

- `QuantumAlg.Core`: pure states, gates, tensor products, measurement, and the
  shared CSLib `TimeM` cost adapter.
- `QuantumAlg.Core.Components`: named gates, kets, oracle and control
  components.
- `QuantumAlg.Primitives`: reusable quantum-algorithm primitives such as phase
  kickback, QSP, LCU, swap test, and amplitude amplification.
- Circuit theorem endpoints: fixed-circuit statements such as Bell-state
  preparation, GHZ-state preparation, and QFT.
- `QuantumAlg.Algorithms`: end-to-end algorithm/protocol statements including
  Deutsch-Jozsa, Bernstein-Vazirani, Grover, QPE, order finding, amplitude
  estimation, teleportation, superdense coding, and Simon.

Trusted cost annotations for query or iterate counts live beside the theorem
endpoints they annotate and use the shared CSLib `TimeM` adapter.

For a quick build check:

```bash
lake exe cache get
lake build
```

For theorem discovery, start from `QuantumAlg.lean` or the module names above.
Lean docstrings cite the source references using keys resolved by
`REFERENCES.json`.

## Quantum machine learning

Lean-QuantumAlg exposes two overlapping views of quantum machine learning:
expressivity, and trainability with Lie-algebraic simulation.

**Expressivity.** Trigonometric polynomials and QSP/QSVT provide the polynomial
transformation substrate, followed by parameter-shift rules, quantum kernels,
and QFIM-based capacity bounds. Verified highlights include:

- [`QuantumAlg.ParameterShiftRule.main`](QuantumAlg/Primitives/ParameterShift.lean),
  an exact parameter-shift identity for frequency-one variational costs.
- [`QuantumAlg.QuantumKernel.main`](QuantumAlg/Primitives/QKernel/Fidelity.lean),
  proving that every finite fidelity-kernel Gram matrix is positive semidefinite.
- [`QuantumAlg.qfim_rank_le_dlaDim`](QuantumAlg/Primitives/QNN/Overparam/QuantumFisherRank.lean)
  and [`QuantumAlg.QFIMOverparam.main`](QuantumAlg/Primitives/QNN/Overparam/OverparamQFIM.lean),
  giving a dynamical-Lie-algebra rank bound and a non-vacuous `su(2)` QFIM onset.

**Trainability.** The main results connect Lie-algebraic variance laws, explicit
no-barren-plateau families, and exact loss reconstruction:

- [Barren-plateau gradient variance](https://qudeleap.github.io/Lean-QuantumAlg/theorems/barren-plateau-variance/)
  derives the reductive Ragone sum from explicit second-moment and Schur inputs;
  Lean: [`QuantumAlg.RagoneReductive.totalVariance_eq`](QuantumAlg/Primitives/QNN/Interface/RagoneInterface.lean).
- [Locality forbids the barren plateau](https://qudeleap.github.io/Lean-QuantumAlg/theorems/locality-no-barren-plateau/)
  gives a genuine product-Clifford local family with constant variance;
  Lean: [`QuantumAlg.localObs_not_hasBarrenPlateau`](QuantumAlg/Primitives/QNN/Algebras/SingleQubitDLA.lean).
- [g-sim transfer-matrix coordinate propagation](https://qudeleap.github.io/Lean-QuantumAlg/theorems/gsim-transfer-matrix/)
  evolves observables in the `dim(g)`-dimensional Lie-algebra coordinate space;
  Lean: [`QuantumAlg.gsimEvolved_coords`](QuantumAlg/Primitives/QNN/Simulation/GSim.lean).
- [Lie-algebraic loss reconstruction](https://qudeleap.github.io/Lean-QuantumAlg/theorems/gsim-correctness/)
  reconstructs the loss exactly from `dim(g)` quantum data;
  Lean: [`QuantumAlg.gsim_loss_reconstruction_ansatz`](QuantumAlg/Primitives/QNN/Simulation/GSim.lean).

Start from the two focused public navigation modules:

```lean
import QuantumAlg.Primitives.QNN.Expressivity
import QuantumAlg.Primitives.QNN.Trainability
```

Bibliographic sources are indexed in [`REFERENCES.json`](REFERENCES.json).

## Contributing and discussion

Issues and pull requests are welcome. Please keep contributions small and
source-backed: algorithm claims should cite public references, and Lean changes
should build without `sorry`, `admit`, or new axioms.

## License

Lean-QuantumAlg is released under the Apache License 2.0. See `LICENSE`.
