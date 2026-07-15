/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularInversion.Resource
public import QuantumAlg.Primitives.EllipticCurve.PointAddition

/-!
# Elliptic-curve resource hooks

This module defines abstract resource hooks for elliptic-curve circuit
families.  The hooks are interface records: concrete source-specific formulas
instantiate them in later resource-profile layers.  The named families mirror
the source resource split into modular inversion/division, controlled
point-addition, and scalar-multiplication costs [RNSL17, ECDLP.tex:650-699],
with later improved tradeoff formulas tracked against the signed-windowed
scalar-multiplication literature [HJN+20, elliptic-curves.tex:20-36].
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve

/-- Circuit families used by the elliptic-curve arithmetic stack. -/
inductive CircuitFamily where
  | inv
  | div
  | ecadd
  | ecmul
deriving DecidableEq

/-- Abstract resource hook for one elliptic-curve circuit family at a selected
bit width.  The `profile` field carries gate/depth counters, while clean and
dirty footprints are kept explicit for later resource statements. -/
structure ResourceHook where
  /-- Bit width of the circuit family represented by this hook. -/
  width : ℕ
  /-- Gate/depth resource profile associated with the hook. -/
  profile : ModularArithmeticResourceProfile
  /-- Clean ancillary qubits required by the hook. -/
  cleanQubits : ℕ
  /-- Dirty ancillary qubits allowed by the hook. -/
  dirtyQubits : ℕ
deriving DecidableEq

namespace ResourceHook

/-- Build an ECC hook directly from a modular-arithmetic profile and explicit
clean/dirty footprint counters. -/
def ofProfile (width : ℕ) (profile : ModularArithmeticResourceProfile)
    (cleanQubits dirtyQubits : ℕ) : ResourceHook where
  width := width
  profile := profile
  cleanQubits := cleanQubits
  dirtyQubits := dirtyQubits

/-- Fieldwise upper-bound relation for abstract ECC resource hooks. -/
structure SupportsUpperBound (hook bound : ResourceHook) : Prop where
  width_eq : hook.width = bound.width
  profile_le :
    ModularArithmeticResourceProfile.SupportsUpperBound hook.profile bound.profile
  cleanQubits_le : hook.cleanQubits ≤ bound.cleanQubits
  dirtyQubits_le : hook.dirtyQubits ≤ bound.dirtyQubits

/-- Every hook supports itself as an exact bound. -/
theorem supportsUpperBound_refl (hook : ResourceHook) :
    SupportsUpperBound hook hook where
  width_eq := rfl
  profile_le := ModularArithmeticResourceProfile.SupportsUpperBound.refl hook.profile
  cleanQubits_le := le_rfl
  dirtyQubits_le := le_rfl

@[simp] theorem ofProfile_width (width : ℕ)
    (profile : ModularArithmeticResourceProfile) (cleanQubits dirtyQubits : ℕ) :
    (ofProfile width profile cleanQubits dirtyQubits).width = width :=
  rfl

@[simp] theorem ofProfile_profile (width : ℕ)
    (profile : ModularArithmeticResourceProfile) (cleanQubits dirtyQubits : ℕ) :
    (ofProfile width profile cleanQubits dirtyQubits).profile = profile :=
  rfl

/-- ECC hook induced by the modular-inversion endpoint parameters. -/
def forInversion (width cleanQubits dirtyQubits : ℕ)
    (params : ModularInversion.ResourceParameters) : ResourceHook :=
  ofProfile width params.toProfile cleanQubits dirtyQubits

/-- ECC hook induced by the modular-division endpoint parameters. -/
def forDivision (width cleanQubits dirtyQubits : ℕ)
    (params : ModularDivision.ResourceParameters) : ResourceHook :=
  ofProfile width params.toProfile cleanQubits dirtyQubits

/-- ECC hook induced by the generic point-addition endpoint parameters. -/
def forPointAddition (width cleanQubits dirtyQubits : ℕ)
    (params : PrimeFieldShortWeierstrass.GenericPointAddition.ResourceParameters) :
    ResourceHook :=
  ofProfile width params.toProfile cleanQubits dirtyQubits

/-- ECC hook induced by the controlled point-addition endpoint parameters. -/
def forControlledPointAddition (width cleanQubits dirtyQubits : ℕ)
    (params : PrimeFieldShortWeierstrass.ControlledPointAddition.ResourceParameters) :
    ResourceHook :=
  ofProfile width params.toProfile cleanQubits dirtyQubits

end ResourceHook

/-- The abstract hook set consumed by elliptic-curve circuit endpoints. -/
structure HookSet where
  /-- Resource hook selected for modular inversion. -/
  inversion : ResourceHook
  /-- Resource hook selected for modular division. -/
  division : ResourceHook
  /-- Resource hook selected for point addition. -/
  pointAddition : ResourceHook
  /-- Resource hook selected for scalar multiplication. -/
  scalarMultiplication : ResourceHook
deriving DecidableEq

namespace HookSet

/-- Select the hook associated to a named ECC circuit family. -/
def get (hooks : HookSet) : CircuitFamily → ResourceHook
  | .inv => hooks.inversion
  | .div => hooks.division
  | .ecadd => hooks.pointAddition
  | .ecmul => hooks.scalarMultiplication

@[simp] theorem get_inv (hooks : HookSet) :
    hooks.get .inv = hooks.inversion :=
  rfl

@[simp] theorem get_div (hooks : HookSet) :
    hooks.get .div = hooks.division :=
  rfl

@[simp] theorem get_ecadd (hooks : HookSet) :
    hooks.get .ecadd = hooks.pointAddition :=
  rfl

@[simp] theorem get_ecmul (hooks : HookSet) :
    hooks.get .ecmul = hooks.scalarMultiplication :=
  rfl

end HookSet

end EllipticCurve
end QuantumAlg
