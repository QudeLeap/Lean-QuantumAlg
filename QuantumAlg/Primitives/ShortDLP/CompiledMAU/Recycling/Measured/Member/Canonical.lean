/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Canonical

/-!
# The same complete two-stream posterior is independent of old output values

The original first and second exponents act on the same unit and reference
coordinates. Actual earlier writes supply every paid feedback phase, so
arbitrary old cell values introduce no restriction [GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (tupleCoordinates)

variable (m ell width : Nat) (modulus : BitVec width) [NeZero modulus.toNat]
  (generator target : (ZMod modulus.toNat)ˣ)

/-- Both original exponent products keep the full same first accumulator/reference posterior. -/
def canonicalMemberSource (Reference : Register) (readout : MemberReadouts m ell) :
    HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) :=
  canonicalExponentSource modulus target⁻¹ true Reference (tupleCoordinates ell readout.2) ell
      0 (by omega) *
    canonicalExponentSource modulus generator true Reference (tupleCoordinates (ell + m) readout.1)
      (ell + m) 0 (by omega)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The complete actual retained-bit source has no dependence on arbitrary original Stores. -/
lemma memberReadoutSource_canonical (Reference : Register)
    (store : Store (context base noQuantum m ell width)) (readout : MemberReadouts m ell) :
    memberReadoutSource base noQuantum m ell width modulus generator target Reference store
        readout =
      canonicalMemberSource m ell width modulus generator target Reference readout := by
  have first := exponentReadoutSource_canonical modulus generator true base noQuantum m ell
    (fun index : Fin (ell + m) => Fin.castAdd ell index) (Fin.castAdd_injective _ _) Reference store
    readout.1
  have separate : Function.Injective (fun index : Fin ell => Fin.natAdd (ell + m) index) := by
    intro first second same
    apply Fin.ext
    have values : ell + m + first.val = ell + m + second.val := congrArg Fin.val same
    omega
  have second := exponentReadoutSource_canonical modulus target⁻¹ true base noQuantum m ell
    (fun index : Fin ell => Fin.natAdd (ell + m) index) separate Reference
    (exponentOutputStore base noQuantum m ell width
      (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store readout.1)
    readout.2
  exact congrArg₂
    (fun left right : HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) =>
      left * right) second first

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
