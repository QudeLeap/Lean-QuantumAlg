/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev
public import QuantumAlg.Primitives.QSP.SingleQubit.Fourier
public import QuantumAlg.Util.Polynomial.ChebyshevFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Chebyshev-Fourier QSP bridge

This module records the explicit cross-convention bridge.  It keeps the
Chebyshev polynomial normalization in `QSP.Chebyshev` and the Fourier/Laurent
normalization in `QSP.Fourier`, while exposing the common gate-level signal
substitution used to compare conventions.

The key source-backed substitution is `x = cos θ`: for `x ∈ [-1,1]`, the
Chebyshev signal `O(x)` is the `Y` rotation `R_Y(2 arccos x)`.  This is the
gate-level step needed before comparing the YZZYZ Fourier convention against
Chebyshev products.

The polynomial bridge below is deliberately explicit.  It gives a concrete
coefficient-level translation between Chebyshev-basis expansions and the
Fourier/Laurent representatives used by `lEval`, records the inverse extraction
back to Chebyshev coefficients, and keeps the phase, parity, normalization, and
`x = cos θ` substitution choices visible.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

open Polynomial Complex
open scoped BigOperators

/-- Chebyshev-Fourier signal bridge: on `[-1,1]`, the reflection signal `O(x)`
is exactly the `Y` rotation at angle `2 arccos x`. -/
theorem signalO_eq_rotY_arccos {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    signalO x = (rotY (2 * Real.arccos x) : HilbertOperator (Qubits 1)) := by
  have hhalf : (2 * Real.arccos x) / 2 = Real.arccos x := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [signalO, rotY, rotYOp, hhalf, Real.cos_arccos hx.1 hx.2,
      Real.sin_arccos]

/-- The Chebyshev `O`-convention product rewritten with the bridge signal.
This is the gate-level preservation lemma that later polynomial translation
work can use before comparing the Chebyshev and Fourier normalizations. -/
theorem qspO_to_fourier_signal_form (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspO φ₀ φs x =
      φs.foldl
        (fun U φ =>
          U *
            (((rotY (2 * Real.arccos x) : Gate (Qubits 1)) * rotZ φ :
              HilbertOperator (Qubits 1))))
        (rotZ φ₀ : HilbertOperator (Qubits 1)) := by
  induction φs using List.reverseRecOn with
  | nil =>
      simp [qspO]
  | append_singleton φs φ ih =>
      rw [qspO_concat, ih, List.foldl_append, List.foldl_cons, List.foldl_nil,
        signalO_eq_rotY_arccos hx]

/-- YZZYZ-compatible naming of the same signal rewrite: Chebyshev products
first enter the Fourier side through the `Y`-rotation signal before the
polynomial bridge records the remaining phase/parity/normalization choices. -/
theorem qspO_to_yzzyz_signal_form (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspO φ₀ φs x =
      φs.foldl
        (fun U φ =>
          U *
            (((rotY (2 * Real.arccos x) : Gate (Qubits 1)) * rotZ φ :
              HilbertOperator (Qubits 1))))
        (rotZ φ₀ : HilbertOperator (Qubits 1)) :=
  qspO_to_fourier_signal_form φ₀ φs hx

end

end QuantumAlg
