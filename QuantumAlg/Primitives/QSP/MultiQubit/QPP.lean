/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QPP.Witness

/-!
# Unitary polynomial transformation (quantum phase processing)

Quantum phase processing (QPP) — equivalently applies a trigonometric
transformation to the *eigenphases* of an `n`-qubit unitary `U` by interleaving
the controlled unitary `c-U` with
single-qubit processing rotations on one ancilla
[WZYW23, arxiv_v3.tex:601]. It is the multi-qubit generalization of the
single-qubit trigonometric QSP (`QuantumAlg.Primitives.QSP.SingleQubit.Fourier`), obtained
by **replacing the signal gate `R_Z(x)` of QSP with `c-U`**
[WZYW23, arxiv_v3.tex:632].

This module formalizes the eigenstate (decoupled) regime, where the target
holds an eigenstate `U|u⟩ = e^{iθ}|u⟩`. The whole construction then collapses
to single-qubit QSP at the signal `x = θ`:

- on `|u⟩`, the signal `c-U` acts on the ancilla as the controlled-phase gate
  `phaseGate θ = diag(1, e^{iθ})` (eigenvalue phase kickback), which is the QSP
  encoding gate `R_Z(θ) = rotZStd θ` up to the global phase `e^{iθ/2}`
  (`phaseGate_signal`);
- consequently the QPP word `qppYZZYZ U φ θ₀ φ₀ ps` (the YZZYZ trainable blocks
  interleaved with `c-U`) on `|ψ⟩ ⊗ |u⟩` equals
  `(e^{iθ/2})^L · (qspYZZYZ φ θ₀ φ₀ ps θ |ψ⟩) ⊗ |u⟩`, i.e. the single-qubit
  YZZYZ word evaluated at the eigenphase, tensored with the untouched
  eigenstate — the **eigenspace decomposition of QPP**
  [WZYW23, arxiv_v3.tex:641].

Composing with the QSP characterization `qsp_yzzyz_iff` gives the phase-evolution
guarantee [WZYW23, arxiv_v3.tex:650]: every trigonometric transform achievable
by single-qubit QSP is realized on the eigenphase of `U` by a QPP word
(`qpp_realizes_target`).

The number of `c-U` calls equals the number of QSP signal slots, so the global
phase here is `(e^{iθ/2})^L`; Wang's alternating `c-U`/`c-U†` convention instead
leaves only the parity phase `(e^{-iθ/2})^{L mod 2}`.

## Main results

- `QuantumAlg.controlled_apply_eigenstate` — on an eigenstate, `c-U` acts on the
  ancilla as the QSP signal gate up to a global phase:
  `c-U (|ψ⟩ ⊗ |u⟩) = (e^{iθ/2} · rotZStd θ |ψ⟩) ⊗ |u⟩`.
- `QuantumAlg.phaseGate_signal` — `diag(1, e^{iθ}) = e^{iθ/2} · R_Z(θ)`,
  the controlled-phase gate as the QSP encoding gate up to global phase.
- `QuantumAlg.QSP.MultiQubit.QPP.eigenstate_decomposition` — the eigenspace decomposition: the QPP
  word on `|ψ⟩ ⊗ |u⟩` is `(e^{iθ/2})^L · (qspYZZYZ … θ |ψ⟩) ⊗ |u⟩`.
- `QuantumAlg.QSP.MultiQubit.QPP.Witness.main` — the public projected-block endpoint: an
  explicit QPP circuit witness block-encodes the unitary polynomial `F(U)`.
- `QuantumAlg.qpp_realizes_target` — every `IsYZPair` transform is realized on
  the eigenphase by some QPP word.
-/

@[expose] public section
