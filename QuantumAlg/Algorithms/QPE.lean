/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Algorithms.QPE.Endpoint

/-!
# Quantum phase estimation

The public endpoint prepares an owned phase register beside the supplied
borrowed eigenstate, executes the controlled-power ladder and inverse QFT,
measures the phase wires into actual classical cells, and packs the result.
Complete Output retains every live system and cell. The same execution
restores the borrowed state jointly with its external reference and satisfies
the original circular-precision guarantee and independent native budgets.
-/
