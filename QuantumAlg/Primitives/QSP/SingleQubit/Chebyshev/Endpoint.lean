/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic

/-!
# Reflection-based QSP polynomial characterization

The phase sequence is chosen once and works for every signal value. Degree,
parity and normalization are both necessary and sufficient
[Lin22, hermfunc.tex:1118-1138].
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing

open Polynomial

/-- Exact polynomial characterization with a single phase sequence valid on the entire interval. -/
public theorem main (d : Nat) (P Q : ℂ[X]) :
    IsQSPPair d P Q ↔
      ∃ (φ₀ : Real) (φs : List Real), φs.length = d ∧
        ∀ (x : Real) (_hx : x ∈ Set.Icc (-1 : Real) 1),
          qspO φ₀ φs x = qspMat P Q x :=
  characterization d P Q

end QuantumAlg.ReflectionBasedQuantumSignalProcessing
