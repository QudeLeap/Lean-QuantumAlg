/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularInversion.Basic
public import QuantumAlg.Primitives.MAU.ModularInversion.Schedule
public import QuantumAlg.Primitives.MAU.ModularInversion.MontgomeryKaliski
public import QuantumAlg.Primitives.MAU.ModularInversion.Resource
public import QuantumAlg.Primitives.MAU.ModularInversion.Layout
public import QuantumAlg.Primitives.MAU.ModularInversion.StructuredCircuit

/-!
# Reversible modular inversion over units

This file is the stable re-export for the modular-inversion basic, schedule,
Montgomery--Kaliski fixed-round state machine, resource, endpoint-witness, and
encoded structured-circuit modules.
-/

@[expose] public section
