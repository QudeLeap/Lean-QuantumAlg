/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Analysis.Haar
public import QuantumAlg.Analysis.QuantumFisher
public import QuantumAlg.Analysis.QuantumFisher.FSBridge
public import QuantumAlg.Analysis.ParameterShift
public import QuantumAlg.Analysis.GeneralizedParameterShift
public import QuantumAlg.Analysis.QNN
public import QuantumAlg.Analysis.Trotter
public import QuantumAlg.Analysis.LinearSystem
public import QuantumAlg.Analysis.QDrift
public import QuantumAlg.Analysis.FTQC.CliffordT.Word
public import QuantumAlg.Analysis.FTQC.CliffordT.Ring
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker
public import QuantumAlg.Analysis.FTQC.CliffordT.Certificates
public import QuantumAlg.Analysis.FTQC.CliffordT.Identities
public import QuantumAlg.Analysis.FTQC.SingleQubit.ZYZ
public import QuantumAlg.Analysis.UnitaryReversal.Amplification
public import QuantumAlg.Analysis.UnitaryReversal.Ancilla
public import QuantumAlg.Analysis.UnitaryReversal.Decoding
public import QuantumAlg.Analysis.UnitaryReversal.EncoderUnitary
public import QuantumAlg.Analysis.UnitaryReversal.Encoding
public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Action
public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Construction
public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Exact
public import QuantumAlg.Analysis.UnitaryReversal.ModifiedAmplification.Parameters
public import QuantumAlg.Analysis.UnitaryReversal.Orthonormality
public import QuantumAlg.Analysis.UnitaryReversal.TargetRotation
public import QuantumAlg.Analysis.Walk.Amplification
public import QuantumAlg.Analysis.Walk.Construction
public import QuantumAlg.Analysis.Walk.Perturbation

/-!
# Quantum information and algorithm analysis

This layer exposes quantum information, variational-model, learning-theory,
Hamiltonian-simulation, walk, spectral linear-system and unitary-reversal results.
It may use the quantum framework and named components, while reusable executable
circuit constructions belong to `QuantumAlg.Primitives`.
-/
