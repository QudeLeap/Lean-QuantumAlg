/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Matrix
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Source

/-!
# Complete two-stream source and retained writes independent of arithmetic histories

The actual first Store feeds the second exponent. Its retained values are
proved equal to the same chronological result writes, so both complete source
products depend only on the retained bits. The second product acts on the
entire first unnormalized unit/reference posterior [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits)

/-- The two original chronological exponent tuples, without integer packing. -/
abbrev MemberReadouts (m ell : Nat) := Bits (ell + m) × Bits ell

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberSourceCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- Every actual arithmetic record of both original streams is retained distinctly. -/
abbrev MemberArithmeticOutcomes :=
  ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := ell + m) generator
      (ell + m) 0 (by omega) ×
    ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := ell) target⁻¹
      ell 0 (by omega)

/-- Exact bijection separating arithmetic histories from the two physically retained bit tuples. -/
def memberOutcomeEquiv : MemberOutcomes base noQuantum m ell width modulus wide generator target ≃
    (MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target ×
      MemberReadouts m ell) :=
  (Equiv.prodCongr
    (exponentOutcomeEquiv base noQuantum m ell width modulus wide (bits := ell + m) generator
      (ell + m) 0 (by omega))
    (exponentOutcomeEquiv base noQuantum m ell width modulus wide (bits := ell) target⁻¹
      ell 0 (by omega))).trans (Equiv.prodProdProdComm _ _ _ _)

/-- The same original chronological result writes of both streams, preserving every other value. -/
def memberReadoutStore (store : Store (MemberSourceCtx base noQuantum m ell width))
    (readout : MemberReadouts m ell) : Store (MemberSourceCtx base noQuantum m ell width) :=
  exponentOutputStore base noQuantum m ell width (fun index : Fin ell => Fin.natAdd (ell + m) index)
    ell 0 (by omega)
    (exponentOutputStore base noQuantum m ell width
      (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store readout.1)
    readout.2

/-- The second source product receives the complete first unit/reference posterior. -/
def memberReadoutSource (Reference : Register)
    (store : Store (MemberSourceCtx base noQuantum m ell width)) (readout : MemberReadouts m ell) :
    HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) :=
  exponentReadoutSource base noQuantum m ell width modulus target⁻¹ true
      (fun index : Fin ell => Fin.natAdd (ell + m) index) Reference ell 0 (by omega)
      (exponentOutputStore base noQuantum m ell width
        (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store readout.1)
      readout.2 *
    exponentReadoutSource base noQuantum m ell width modulus generator true
      (fun index : Fin (ell + m) => Fin.castAdd ell index) Reference (ell + m) 0 (by omega) store
      readout.1

private lemma member_source_projection (Reference : Register)
    (store : Store (MemberSourceCtx base noQuantum m ell width))
    (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target)
    (readout : MemberReadouts m ell) :
    memberSourceKraus base noQuantum m ell width modulus wide generator target Reference store
        ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout)) =
      exponentSourceKraus base noQuantum m ell width modulus wide target⁻¹ true
          (secondCell base noQuantum m ell width) Reference ell 0 (by omega)
          (exponentActualRecord base noQuantum m ell width modulus wide generator true
            (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store
            ((exponentOutcomeEquiv base noQuantum m ell width modulus wide generator (ell + m) 0
              (by omega)).symm (arithmetic.1, readout.1))).1
          ((exponentOutcomeEquiv base noQuantum m ell width modulus wide target⁻¹ ell 0
            (by omega)).symm (arithmetic.2, readout.2)) *
        exponentSourceKraus base noQuantum m ell width modulus wide generator true
          (firstCell base noQuantum m ell width) Reference (ell + m) 0 (by omega) store
          ((exponentOutcomeEquiv base noQuantum m ell width modulus wide generator (ell + m) 0
            (by omega)).symm (arithmetic.1, readout.1)) := rfl

/-- All actual arithmetic histories give the same complete retained-bit two-stream source. -/
lemma memberSourceKraus_readout (Reference : Register)
    (store : Store (MemberSourceCtx base noQuantum m ell width))
    (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target)
    (readout : MemberReadouts m ell) :
    memberSourceKraus base noQuantum m ell width modulus wide generator target Reference store
        ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout)) =
      memberReadoutSource base noQuantum m ell width modulus generator target Reference store
        readout := by
  have first := exponentSourceKraus_readout base noQuantum m ell width modulus wide generator true
    (fun index : Fin (ell + m) => Fin.castAdd ell index) Reference (ell + m) 0 (by omega) store
    store (fun _ => rfl) arithmetic.1 readout.1
  have preserved := exponentRecord_resultStoreAgree base noQuantum m ell width
    (fun index : Fin (ell + m) => Fin.castAdd ell index) modulus wide generator true (ell + m) 0
    (by omega) store store (fun _ => rfl) arithmetic.1 readout.1
  have second := exponentSourceKraus_readout base noQuantum m ell width modulus wide target⁻¹ true
    (fun index : Fin ell => Fin.natAdd (ell + m) index) Reference ell 0 (by omega)
    (exponentActualRecord base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store
      ((exponentOutcomeEquiv base noQuantum m ell width modulus wide generator (ell + m) 0
        (by omega)).symm (arithmetic.1, readout.1))).1
    (exponentOutputStore base noQuantum m ell width
      (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store readout.1)
    preserved arithmetic.2 readout.2
  rw [member_source_projection]
  exact congrArg₂
    (fun left right : HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference) =>
      left * right) second first

omit [NeZero modulus.toNat] in
/-- Real vent writes in either exponent leave exactly the two original retained result tuples. -/
lemma memberRecord_resultStoreAgree
    (store : Store (MemberSourceCtx base noQuantum m ell width))
    (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target)
    (readout : MemberReadouts m ell) :
    ResultStoreAgree base noQuantum m ell width
      (memberActualRecord base noQuantum m ell width modulus wide generator target store
        ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout))).1
      (memberReadoutStore base noQuantum m ell width store readout) := by
  have first := exponentRecord_resultStoreAgree base noQuantum m ell width
    (fun index : Fin (ell + m) => Fin.castAdd ell index) modulus wide generator true (ell + m) 0
    (by omega) store store (fun _ => rfl) arithmetic.1 readout.1
  have second := exponentRecord_resultStoreAgree base noQuantum m ell width
    (fun index : Fin ell => Fin.natAdd (ell + m) index) modulus wide target⁻¹ true ell 0 (by omega)
    (exponentActualRecord base noQuantum m ell width modulus wide generator true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) store
      ((exponentOutcomeEquiv base noQuantum m ell width modulus wide generator (ell + m) 0
        (by omega)).symm (arithmetic.1, readout.1))).1
    (exponentOutputStore base noQuantum m ell width
      (fun index : Fin (ell + m) => Fin.castAdd ell index) (ell + m) 0 (by omega) store readout.1)
    first arithmetic.2 readout.2
  exact second

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
