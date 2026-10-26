# Lean-QuantumAlg

<p align="center">
  <a href="https://github.com/leanprover/lean4/releases/tag/v4.33.1"><img src="https://img.shields.io/badge/Lean-v4.33.1-6C5CE7" alt="Lean v4.33.1"></a>
  <a href="https://arxiv.org/abs/2610.30216"><img src="https://img.shields.io/badge/arXiv-2610.30216-b31b1b.svg" alt="QuantumAlg on arXiv"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/License-Apache%202.0-blue.svg" alt="Apache License 2.0"></a>
</p>

<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset=".github/architecture-dark.png">
    <source media="(prefers-color-scheme: light)" srcset=".github/architecture-light.png">
    <img alt="Lean-QuantumAlg architecture: Util, Core, Components, Analysis, Primitives, and Algorithms." src=".github/architecture-light.png" width="864">
  </picture>
</p>

Lean-QuantumAlg is a Lean 4 framework built on mathlib for AI agents to verify quantum algorithms. It derives probabilities, final states and resource use from one execution in an explicit model. It aims to:

- Bind correctness, borrowed-state restoration and resource bounds to one execution.
- Make specifications and execution models explicit for human review.
- Provide reusable, source-backed components following mathlib conventions.

## Cite this repository

If you use Lean-QuantumAlg in your work or its Algorithm–Solves–Problem structure to develop new algorithms, please cite:

```bibtex
@misc{leanquantumalg,
  title={Lean-QuantumAlg: A Framework for {AI} Agents to Produce Quantum Algorithms that Humans Can Trust},
  author={Lei Zhang and Mingrui Jing and Yusheng Zhao and Jiahong Liu and Xin Wang},
  year={2026},
  eprint={2610.30216},
  archivePrefix={arXiv},
  primaryClass={quant-ph},
  url={https://arxiv.org/abs/2610.30216},
}
```

See [quantum machine learning analysis](#quantum-machine-learning-analysis) and [quantum attacks on public-key cryptography](#quantum-attacks-on-public-key-cryptography) for citations of specific results.

## Using Lean-QuantumAlg in your project

To add Lean-QuantumAlg as a dependency to a Lake project, add the following to your `lakefile.toml`:

```toml
[[require]]
name = "QuantumAlg"
git = "https://github.com/QudeLeap/Lean-QuantumAlg.git"
rev = "3.4.1"
```

> Starting with 3.4.0, Linux x86_64 releases include a precompiled library cache.

Use Lean `v4.33.1`. Then import either the aggregate module or a focused module:

```lean
import QuantumAlg
import QuantumAlg.Algorithms.Grover
import QuantumAlg.Algorithms.QPE
import QuantumAlg.Primitives.QFT
```

To build a checkout from source, including on other platforms, run `lake build`.

For theorem discovery, browse the [public theorem catalog](https://qudeleap.github.io/Lean-QuantumAlg/). Bibliographic sources are indexed in [REFERENCES.json](REFERENCES.json), where each key is a source reference used in the Lean docstrings.

### Quantum machine learning analysis

Lean-QuantumAlg exposes two overlapping views of quantum machine learning: expressivity and trainability with Lie-algebraic simulation. For expressivity, trigonometric polynomials and QSP/QSVT provide the polynomial transformation substrate, followed by parameter-shift rules, quantum kernels, and QFIM-based capacity bounds. For trainability, the main results connect explicit no-barren-plateau families, Lie-algebraic simulation, and exact loss reconstruction.

For these QML formalizations, cite the QNN paper: [![arXiv:2607.12981](https://img.shields.io/badge/arXiv-2607.12981-b31b1b.svg)](https://arxiv.org/abs/2607.12981).

Start from the following modules:

```lean
import QuantumAlg.Analysis.QNN.Expressivity
import QuantumAlg.Analysis.QNN.Trainability
import QuantumAlg.Primitives.QML
```

### Quantum attacks on public-key cryptography

Lean-QuantumAlg formalizes quantum algorithms for integer factoring and finite-cyclic discrete logarithms, including attacks on RSA-2048 and P-256. Each algorithm endpoint states an independent problem and proves that an algorithm solves it under an explicit execution model. Correctness, borrowed-state restoration and logical-resource bounds refer to the same execution, with the input conditions and success guarantees stated in the theorem's specification.

For these cryptanalysis formalizations, cite the Shor paper: [![arXiv:2607.14082](https://img.shields.io/badge/arXiv-2607.14082-b31b1b.svg)](https://arxiv.org/abs/2607.14082).

Start from the following modules:

```lean
import QuantumAlg.Algorithms.Factoring
import QuantumAlg.Algorithms.FiniteCyclicDLP
import QuantumAlg.Algorithms.EllipticCurve
```

## Contributing and discussion

Issues and pull requests are welcome. Please keep contributions small and source-backed: algorithm claims should cite public references, and Lean changes should build without `sorry`, `admit`, or new axioms.

## License

Lean-QuantumAlg is released under the Apache License 2.0. See [LICENSE](LICENSE).
