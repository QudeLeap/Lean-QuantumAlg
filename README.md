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

## Contributing and discussion

Issues and pull requests are welcome. Please keep contributions small and
source-backed: algorithm claims should cite public references, and Lean changes
should build without `sorry`, `admit`, or new axioms.

## License

Lean-QuantumAlg is released under the Apache License 2.0. See `LICENSE`.
