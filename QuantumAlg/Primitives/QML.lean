/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.QNN.Expressivity
public import QuantumAlg.Primitives.QSP
public import QuantumAlg.Primitives.QKernel

/-!
# Quantum machine learning constructions and expressivity

This family aggregate connects the variational-model and QFIM theory in
`QuantumAlg.Analysis.QNN.Expressivity` with the QSP, QPP, QSVT, and quantum-kernel
primitive families. The theory aggregate is independently importable and does
not depend on these circuit constructions.
-/
