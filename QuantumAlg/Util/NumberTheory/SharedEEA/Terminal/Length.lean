/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Tail
import all QuantumAlg.Util.NumberTheory.SharedEEA.Length.Pair

/-!
# Actual length refresh at the first terminal shift-counter wrap

The source's coefficient-length update relies on the stored old length
being the length read from the post-swap second word
[LYL+26, sec_circuit/sub_block_new.tex:211-219]. At a genuine macro
boundary that premise follows from the established phase invariants.
The finite terminal shift counter can also trigger the same whole-word
swap and length-update condition
[LYL+26, sec_EEA/sub_regshare.tex:22-23,306-315].

The concrete smallest-input terminal trajectory below is sent through
the actual finite serial-XOR length updates. At its first wrap, the old
read length no longer equals the retained coefficient length. The two
registers therefore remain reversibly updated data, but the refreshed
coefficient register does not equal the new read length. This witnesses
the precise missing invariant for extending the macro-boundary proof
to the source's unqualified terminal padding. No idle step or corrected
tail is substituted here, and no later trajectory is inferred from this
counterexample.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.TerminalLength

/-- The smallest-input terminal trajectory reaches its first wrap with retained parity. -/
def smallestWrap : TerminalTail.Frame 5 2 :=
  TerminalTail.repeatPrefix 4 (TerminalTail.start (9 : BitVec 5) (16 : BitVec 5) true)

/-- At overflow exchange, the actual old read length disagrees with the retained old register. -/
lemma old_read_length_mismatch :
    (PhysicalWindow.read 5 smallestWrap.secondWord).toNat.size = 5 ∧
      (2 : BitVec 2).toNat = 2 ∧
      (PhysicalWindow.read 5 smallestWrap.secondWord).toNat.size ≠ (2 : BitVec 2).toNat := by
  decide

/-- Actual serial XOR refresh at the overflow exchange does not produce the new read length. -/
lemma refreshed_length_mismatch :
    let refreshed := LengthPair.update smallestWrap.firstWord smallestWrap.secondWord
      ((2 : BitVec 2), (0 : BitVec 2))
    refreshed.1.toNat = 1 ∧ refreshed.2.toNat = 1 ∧
      (PhysicalWindow.read 5 smallestWrap.firstWord).toNat.size = 2 ∧
      refreshed.1.toNat ≠ (PhysicalWindow.read 5 smallestWrap.firstWord).toNat.size := by
  decide

/-- The actual mismatched length values still retain the information required by inverse writes. -/
lemma overflow_refresh_reversible :
    LengthPair.rewind smallestWrap.firstWord smallestWrap.secondWord
        (LengthPair.update smallestWrap.firstWord smallestWrap.secondWord
          ((2 : BitVec 2), (0 : BitVec 2))) = ((2 : BitVec 2), (0 : BitVec 2)) :=
  LengthPair.rewind_update _ _ _

end QuantumAlg.NumberTheory.SharedEEA.TerminalLength
