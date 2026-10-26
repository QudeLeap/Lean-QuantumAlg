/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace.Reuse.Words

/-!
# Numerical readouts of the actual full reused initial label

All readout identities are proved before fixing the word width. The saved
physical word is explicitly reversed; no executed wire permutation or
numerical SWAP is substituted for the actual three-layer final swap.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned

private lemma reuse_initial_grouped (modulus : Nat)
    (input saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    (WorkspaceReuse.placement modulus.size).grouping
        (ControlledResidentReuse.initial modulus input saved pool flags).1 =
      (ControlledResident.initial modulus input saved pool flags).1 :=
  congrArg Prod.fst ((ControlledResidentReuse.layout modulus.size).grouping.apply_symm_apply
    (ControlledResident.initial modulus input saved pool flags))

private lemma initial_largeWord_zero (modulus : Nat)
    (input saved : Fin (2 ^ modulus.size)) (pool : Pool modulus.size)
    (flags : ControlledResidentFrame.Flags) :
    WorkspaceReuse.largeWord (ControlledResident.initial modulus input saved pool flags).1 = 0 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  change (BitVec.setWidth modulus.size
    (ControlledResident.initial modulus input saved pool flags).1.1.1.firstWord.reverse).getLsbD
      index.val = (0 : Nat).testBit index.val
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  simp only [index.isLt, decide_true, Bool.true_and, Nat.zero_testBit]
  exact MAU.Inversion.SharedEEA.InitialPortProgram.inputFrame_large_bit modulus input index

private lemma reverseWord_zero (width : Nat) :
    WorkspaceReuse.reverseWord (0 : Fin (2 ^ width)) = 0 := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  change (BitVec.ofFin (0 : Fin (2 ^ width))).reverse.getLsbD index.val =
    (0 : Nat).testBit index.val
  rw [BitVec.getLsbD_reverse]
  change (0 : BitVec width).getMsbD index.val = (0 : Nat).testBit index.val
  exact (BitVec.getMsbD_zero (w := width) (i := index.val)).trans
    (Nat.zero_testBit index.val).symm

/-- Reused A retains the actual saved physical word with its necessary numerical reversal. -/
lemma reusedInitial_work1 (modulus : Nat) (input saved : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    WorkspaceReuse.largeWord (ControlledResidentReuse.initial modulus input saved pool flags).1 =
      WorkspaceReuse.reverseWord saved := by
  have actual := congrArg (fun state : OutputCopy.Data modulus.size => state.2)
    (reuse_initial_grouped modulus input saved pool flags)
  have read := WorkspaceReuse.grouping_numerator modulus.size
    (ControlledResidentReuse.initial modulus input saved pool flags).1
  have reversed := read.symm.trans
    (actual.trans (ControlledResident.initial_numerator modulus input saved pool flags))
  have reflected := congrArg (WorkspaceReuse.reverseWord (width := modulus.size)) reversed
  simpa only [WorkspaceReuse.reverseWord_reverseWord] using reflected

/-- The same actual initial source has zero on the physically reused Y payload. -/
lemma reusedInitial_numerator (modulus : Nat) (input saved : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (ControlledResidentReuse.initial modulus input saved pool flags).1.2 = 0 := by
  have actual := congrArg (WorkspaceReuse.largeWord (width := modulus.size))
    (reuse_initial_grouped modulus input saved pool flags)
  have read := WorkspaceReuse.grouping_largeWord modulus.size
    (ControlledResidentReuse.initial modulus input saved pool flags).1
  have reversed := read.symm.trans
    (actual.trans (initial_largeWord_zero modulus input saved pool flags))
  have reflected := congrArg (WorkspaceReuse.reverseWord (width := modulus.size)) reversed
  simpa only [WorkspaceReuse.reverseWord_reverseWord, reverseWord_zero] using reflected

/-- The original numerical denominator retains its complete physical word orientation. -/
lemma reusedInitial_work2 (modulus : Nat) (input saved : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    ControlledResidentFrame.value
      (ControlledResidentReuse.initial modulus input saved pool flags) = input := by
  have retained : MAU.Inversion.SharedEEA.OutputCopy.value
        ((WorkspaceReuse.placement modulus.size).grouping
          (ControlledResidentReuse.initial modulus input saved pool flags).1).1.1 =
      ControlledResidentFrame.value
        (ControlledResidentReuse.initial modulus input saved pool flags) :=
    congrArg (fun word : BitVec (modulus.size + 3) =>
      BitVec.equivFin (word.reverse.setWidth modulus.size))
      (WorkspaceReuse.grouping_secondWord modulus.size
        (ControlledResidentReuse.initial modulus input saved pool flags).1)
  have actual := congrArg (fun state : OutputCopy.Data modulus.size =>
    MAU.Inversion.SharedEEA.OutputCopy.value state.1.1)
    (reuse_initial_grouped modulus input saved pool flags)
  exact retained.symm.trans
    (actual.trans (ControlledResident.initial_value modulus input saved pool flags))

/-- All original scan-pool coordinates have the supplied actual value after the same adjoint. -/
lemma reusedInitial_pool (modulus : Nat) (input saved : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (ControlledResidentReuse.initial modulus input saved pool flags).1.1.2 = pool := by
  have retained := WorkspaceReuse.grouping_pool modulus.size
    (ControlledResidentReuse.initial modulus input saved pool flags).1
  have actual := congrArg (fun state : OutputCopy.Data modulus.size => state.1.2)
    (reuse_initial_grouped modulus input saved pool flags)
  exact retained.symm.trans
    (actual.trans (ControlledResident.initial_pool modulus input saved pool flags))

/-- C, genuine or temporary N, and arbitrary W retain their separate original values. -/
lemma reusedInitial_flags (modulus : Nat) (input saved : Fin (2 ^ modulus.size))
    (pool : Pool modulus.size) (flags : ControlledResidentFrame.Flags) :
    (ControlledResidentReuse.initial modulus input saved pool flags).2 = flags :=
  (congrArg Prod.snd
    ((ControlledResidentReuse.layout modulus.size).grouping.apply_symm_apply
      (ControlledResident.initial modulus input saved pool flags))).trans
        (ControlledResident.initial_flags modulus input saved pool flags)

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
