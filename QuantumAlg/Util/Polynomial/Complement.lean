/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Complement.Interval.Witness
public import QuantumAlg.Util.Polynomial.Complement.Laurent.Witness

/-!
# Polynomial complement constructions

This module re-exports quantum-free complement and factorization helpers used by
QSP, QPP, and QSVT phase-synthesis arguments.  The interval side supports
bounded real-polynomial completion; the Laurent side supports unit-circle
trigonometric completion.
-/

@[expose] public section
