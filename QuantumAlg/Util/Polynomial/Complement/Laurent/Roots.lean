/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Laurent.Problem

/-!
# Laurent complement roots

Stage module for reciprocal-conjugate root symmetry and multiplicity facts.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

namespace Complement.Laurent.Roots

/-- The inverse-conjugate root pairing `z ↦ 1 / z*` used in Wang's Laurent
complement proof [WZYW23, arxiv_v3.tex:2241-2248]. -/
def reciprocalConj (z : ℂ) : ℂ :=
  (starRingEnd ℂ z)⁻¹

end Complement.Laurent.Roots

end

end QuantumAlg
