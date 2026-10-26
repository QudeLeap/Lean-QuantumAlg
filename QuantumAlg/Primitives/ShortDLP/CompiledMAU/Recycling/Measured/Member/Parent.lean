/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Preservation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Kernel
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Store

/-!
# The actual member kernel retains the entire original parent Store

Every original parent storage reference is physically outside both real
measurement banks. The actual observer retains that complete parent Store
and both exponent tuples; arithmetic-record invariance is proved from the
real writes, without narrowing incoming values [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberParentCtx := context base noQuantum m ell width

/-- Every complete original actual member record preserves the entire incoming parent Store. -/
lemma memberActualRecord_parentStore (modulus : BitVec width) (wide : 2 ≤ width)
    (generator target : (ZMod modulus.toNat)ˣ)
    (store : Store (MemberParentCtx base noQuantum m ell width))
    (outcomes : MemberOutcomes base noQuantum m ell width modulus wide generator target) :
    parentStore base noQuantum m ell width
        (memberActualRecord base noQuantum m ell width modulus wide generator target store
          outcomes).1 = parentStore base noQuantum m ell width store := by
  apply Store.store_eq_of_storage_reads
  intro shape observed
  rw [measuredParentStore_read, measuredParentStore_read]
  exact memberActualRecord_read_other base noQuantum m ell width
    ((parentTransport base noQuantum m ell width).liftStorage observed)
    (fun vent => measuredParentTransport_cell_distinct base noQuantum m ell width observed
      (Fin.natAdd (resultBits m ell) vent))
    (fun result => measuredParentTransport_cell_distinct base noQuantum m ell width observed
      (Fin.castAdd (width - 2) result)) modulus wide generator target store outcomes

/-- Canonical original exponent-result writes preserve the identical complete parent Store. -/
lemma memberReadoutStore_parentStore (store : Store (MemberParentCtx base noQuantum m ell width))
    (readout : MemberReadouts m ell) :
    parentStore base noQuantum m ell width
        (memberReadoutStore base noQuantum m ell width store readout) =
      parentStore base noQuantum m ell width store := by
  apply Store.store_eq_of_storage_reads
  intro shape observed
  rw [measuredParentStore_read, measuredParentStore_read]
  exact memberReadoutStore_read_other base noQuantum m ell width
    ((parentTransport base noQuantum m ell width).liftStorage observed)
    (fun result => measuredParentTransport_cell_distinct base noQuantum m ell width observed
      (Fin.castAdd (width - 2) result)) store readout

/-- The finite observer retains every parent value beside the original real measured tuples. -/
def memberParentObservation (store : Store (MemberParentCtx base noQuantum m ell width)) :
    Store base × CShape.Value (.fixedVector (resultBits m ell) (.finite 2)) :=
  (parentStore base noQuantum m ell width store,
    (resultRead base noQuantum m ell width).eval store)

/-- Arithmetic-history invariance of the complete parent observer follows from actual addresses. -/
lemma memberParentObservation_agrees (modulus : BitVec width) (wide : 2 ≤ width)
    (generator target : (ZMod modulus.toNat)ˣ)
    (store : Store (MemberParentCtx base noQuantum m ell width))
    (arithmetic : MemberArithmeticOutcomes base noQuantum m ell width modulus wide generator target)
    (readout : MemberReadouts m ell) :
    memberParentObservation base noQuantum m ell width
      (memberActualRecord base noQuantum m ell width modulus wide generator target store
        ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout))).1 =
      memberParentObservation base noQuantum m ell width
        (memberReadoutStore base noQuantum m ell width store readout) := by
  apply Prod.ext
  · exact (memberActualRecord_parentStore base noQuantum m ell width modulus wide generator target
      store _).trans (memberReadoutStore_parentStore base noQuantum m ell width store readout).symm
  · exact congrArg CShape.Value.fixedVector
      (funext (memberRecord_resultStoreAgree base noQuantum m ell width modulus wide generator
        target store arithmetic readout))

/-- The canonical observer keeps the same parent Store and exactly both original measured tuples. -/
lemma memberParentObservation_readout (store : Store (MemberParentCtx base noQuantum m ell width))
    (readout : MemberReadouts m ell) :
    memberParentObservation base noQuantum m ell width
        (memberReadoutStore base noQuantum m ell width store readout) =
      (parentStore base noQuantum m ell width store, memberReadoutValue m ell readout) :=
  Prod.ext (memberReadoutStore_parentStore base noQuantum m ell width store readout)
    (memberReadoutStore_resultRead base noQuantum m ell width store readout)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
