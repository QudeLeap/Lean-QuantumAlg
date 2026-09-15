/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear isometry utilities

This file contains small finite-dimensional inner-product-space helpers used by
matrix trace-norm infrastructure.
-/

@[expose] public section

namespace LinearIsometryEquiv

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Finite-dimensional inner product spaces with the same dimension are
linearly isometric. -/
noncomputable def ofFinrankEq (h : Module.finrank 𝕜 E = Module.finrank 𝕜 F) :
    E ≃ₗᵢ[𝕜] F :=
  let bE := stdOrthonormalBasis 𝕜 E
  let bF := stdOrthonormalBasis 𝕜 F
  let e : Fin (Module.finrank 𝕜 E) ≃ Fin (Module.finrank 𝕜 F) := finCongr h
  bE.repr.trans <|
    (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e).trans bF.repr.symm

end LinearIsometryEquiv
