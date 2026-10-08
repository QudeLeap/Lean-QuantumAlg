/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Util.Classical.OrderRecovery
public import QuantumAlg.Util.Order.Finding

/-!
# Independent classical recovery specification

The source modulus, canonical reduced base and fixed-width recovery task
depend only on the original number-theoretic input and the declared oracle
capacity. No runtime or output distribution enters these definitions.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

/-- Source modulus and its original target-capacity certificate. -/
@[expose] public def modulusSpec {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    ClassicalAlgorithms.Modular.ModulusSpec width where
  modulus := N
  two_le := hinput.modulus_ge_two
  le_capacity := access.register_fits

/-- The canonical reduced source base, before runtime encoding. -/
public def baseResidue {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    ClassicalAlgorithms.Modular.Residue (modulusSpec hinput access) :=
  ⟨x % N, Nat.mod_lt x access.modulus_pos⟩

/-- The intrinsic recovery problem with the original source modulus and phase width. -/
@[expose] public def recoverySpec {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    ClassicalAlgorithms.OrderRecovery.Spec width t :=
  ⟨modulusSpec hinput access⟩

/-- Pure fixed-width input for recovery of one actual phase-bit outcome. -/
public def semanticInput {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (outcome : ClassicalAlgorithms.OrderRecovery.TerminalBits t) :
    ClassicalAlgorithms.OrderRecovery.Input (recoverySpec hinput access) :=
  { base := ⟨x % N,
      lt_of_lt_of_le (Nat.mod_lt x access.modulus_pos) access.register_fits⟩
    baseInDomain := Nat.mod_lt x access.modulus_pos
    baseCoprime := (ZMod.coprime_mod_iff_coprime x N).2 hinput.coprime
    terminalBits := outcome }

end

end QuantumAlg.OrderFinding.ShorSourceJoint
