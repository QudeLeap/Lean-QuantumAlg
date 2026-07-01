/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement

/-!
# QSVT polynomial pairs

Stage module for QSVT phase-certificate and completed pair handoff data.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open Polynomial

namespace QSVT.Pair

/-- Namespace-local spelling of the real bounded matching-parity source package. -/
abbrev RealBoundedMatchingParity (d : ℕ) (PRe : ℝ[X]) :=
  QuantumAlg.ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity d PRe

/-- Namespace-local spelling of a single-qubit QSP phase certificate. -/
abbrev PhaseCertificate (d : ℕ) (P Q : ℂ[X]) :=
  QuantumAlg.ReflectionQSPPhaseSynthesis.PhaseCertificate d P Q

/-- Namespace-local spelling of the real bounded phase certificate. -/
abbrev RealBoundedPhaseCertificate (d : ℕ) (PRe : ℝ[X]) :=
  QuantumAlg.ReflectionQSPPhaseSynthesis.RealBoundedPhaseCertificate d PRe

end QSVT.Pair

end QSP.MultiQubit

end QuantumAlg
