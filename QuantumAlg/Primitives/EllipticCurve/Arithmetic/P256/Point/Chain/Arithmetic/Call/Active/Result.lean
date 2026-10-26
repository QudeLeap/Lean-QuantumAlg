/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Readout

/-!
# Complete numerical readouts of the actual reused inversion result

The symbolic-width placement retains the physical saved word, the whole
pool and all three external flags. Its physically reset Y is zero; the
original X word contains the actual finite modular inverse. The saved A
word has the same explicit numerical reversal as at the reused initial
boundary. These are readouts of the actual complete grouping.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma reuse_result_grouped (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (WorkspaceReuse.placement modulus.size).grouping
        (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1 =
      (ControlledResident.result modulus input positive bounded saved pool flags).1 :=
  congrArg Prod.fst ((ControlledResidentReuse.layout modulus.size).grouping.apply_symm_apply
    (ControlledResident.result modulus input positive bounded saved pool flags))

lemma reusedResult_work1 (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    WorkspaceReuse.largeWord
        (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1 =
      WorkspaceReuse.reverseWord saved := by
  have actual := congrArg (fun state : OutputCopy.Data modulus.size => state.2)
    (reuse_result_grouped modulus input positive bounded saved pool flags)
  have read := WorkspaceReuse.grouping_numerator modulus.size
    (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1
  have reversed := read.symm.trans
    (actual.trans (ControlledResident.result_numerator modulus input positive bounded saved
      pool flags))
  have reflected := congrArg (WorkspaceReuse.reverseWord (width := modulus.size)) reversed
  simpa only [WorkspaceReuse.reverseWord_reverseWord] using reflected

lemma reusedResult_numerator (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (saved : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1.2 = 0 := by
  have actual := congrArg (WorkspaceReuse.largeWord (width := modulus.size))
    (reuse_result_grouped modulus input positive bounded saved pool flags)
  have read := WorkspaceReuse.grouping_largeWord modulus.size
    (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1
  have reversed := read.symm.trans
    (actual.trans (ControlledResident.result_work1_zero modulus input coprime positive bounded
      saved pool flags))
  have reflected := congrArg (WorkspaceReuse.reverseWord (width := modulus.size)) reversed
  simpa only [WorkspaceReuse.reverseWord_reverseWord, reverseWord_zero] using reflected

lemma reusedResult_work2 (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.value
        (ControlledResidentReuse.result modulus input positive bounded saved pool flags) =
      NumberTheory.SharedEEA.InverseOutput.word modulus input.val positive bounded := by
  have retained : MAU.Inversion.SharedEEA.OutputCopy.value
        ((WorkspaceReuse.placement modulus.size).grouping
          (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1).1.1 =
      ControlledResidentFrame.value
        (ControlledResidentReuse.result modulus input positive bounded saved pool flags) :=
    congrArg (fun word : BitVec (modulus.size + 3) =>
      BitVec.equivFin (word.reverse.setWidth modulus.size))
      (WorkspaceReuse.grouping_secondWord modulus.size
        (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1)
  have actual := congrArg (fun state : OutputCopy.Data modulus.size =>
    MAU.Inversion.SharedEEA.OutputCopy.value state.1.1)
    (reuse_result_grouped modulus input positive bounded saved pool flags)
  exact retained.symm.trans
    (actual.trans (ControlledResident.result_value modulus input positive bounded saved pool
      flags))

lemma reusedResult_pool (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1.1.2 =
      pool := by
  have retained := WorkspaceReuse.grouping_pool modulus.size
    (ControlledResidentReuse.result modulus input positive bounded saved pool flags).1
  have actual := congrArg (fun state : OutputCopy.Data modulus.size => state.1.2)
    (reuse_result_grouped modulus input positive bounded saved pool flags)
  exact retained.symm.trans
    (actual.trans (ControlledResident.result_pool modulus input positive bounded saved pool flags))

lemma reusedResult_flags (modulus : Nat) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (ControlledResidentReuse.result modulus input positive bounded saved pool flags).2 = flags :=
  (congrArg Prod.snd
    ((ControlledResidentReuse.layout modulus.size).grouping.apply_symm_apply
      (ControlledResident.result modulus input positive bounded saved pool flags))).trans
        (ControlledResident.result_flags modulus input positive bounded saved pool flags)

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
