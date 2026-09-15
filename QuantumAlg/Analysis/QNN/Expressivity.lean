/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Polynomial.Trigonometric
public import QuantumAlg.Analysis.ParameterShift
public import QuantumAlg.Analysis.GeneralizedParameterShift
public import QuantumAlg.Analysis.QNN.Ansatz
public import QuantumAlg.Analysis.QNN.Overparam

/-!
# Quantum learning expressivity theory

This aggregate connects trigonometric cost representations and their exact
parameter-shift rules with variational ansatzes and the QFIM-rank capacity
ceiling. It exposes the theoretical expressivity API independently of quantum
circuit constructions. `QuantumAlg.Primitives.QML` combines this API with the
QSP and quantum-kernel primitive families.
-/
