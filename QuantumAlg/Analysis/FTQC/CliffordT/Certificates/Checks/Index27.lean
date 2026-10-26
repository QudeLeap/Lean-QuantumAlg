/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word27Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word27State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word27Step0 :
    word27Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word27State1 := by decide +kernel

private def word27Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word27State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word27Step1 :
    word27Chunk1.foldl (fun acc a => a.applyPacked acc)
      word27State1 = word27State2 := by decide +kernel

private def word27Chunk2 : List Letter := [.h, .s, .h, .s, .t, .h, .t, .h]
private def word27State3 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word27Step2 :
    word27Chunk2.foldl (fun acc a => a.applyPacked acc)
      word27State2 = word27State3 := by decide +kernel

private def word27Chunk3 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word27State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word27Step3 :
    word27Chunk3.foldl (fun acc a => a.applyPacked acc)
      word27State3 = word27State4 := by decide +kernel

private def word27Chunk4 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word27State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word27Step4 :
    word27Chunk4.foldl (fun acc a => a.applyPacked acc)
      word27State4 = word27State5 := by decide +kernel

private def word27Chunk5 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word27State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word27Step5 :
    word27Chunk5.foldl (fun acc a => a.applyPacked acc)
      word27State5 = word27State6 := by decide +kernel

private def word27Chunk6 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word27State7 : PackedMat2 :=
    ⟨⟨⟨((19 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((19 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word27Step6 :
    word27Chunk6.foldl (fun acc a => a.applyPacked acc)
      word27State6 = word27State7 := by decide +kernel

private def word27Chunk7 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word27State8 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((33 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 6),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 6)⟩,
       ⟨((-33 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word27Step7 :
    word27Chunk7.foldl (fun acc a => a.applyPacked acc)
      word27State7 = word27State8 := by decide +kernel

private def word27Chunk8 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word27State9 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 6),
        ((-29 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((29 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-29 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 7)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-27 : Dyadic) * half ^ 6),
        ((-29 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-19 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word27Step8 :
    word27Chunk8.foldl (fun acc a => a.applyPacked acc)
      word27State8 = word27State9 := by decide +kernel

private def word27Chunk9 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word27State10 : PackedMat2 :=
    ⟨⟨⟨((-87 : Dyadic) * half ^ 7),
        ((-1 : Dyadic) * half ^ 8)⟩,
       ⟨((-1 : Dyadic) * half ^ 6),
        ((-77 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-29 : Dyadic) * half ^ 7),
        ((-61 : Dyadic) * half ^ 8)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((67 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 7),
        ((-59 : Dyadic) * half ^ 8)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((39 : Dyadic) * half ^ 7),
        ((89 : Dyadic) * half ^ 8)⟩,
       ⟨((-19 : Dyadic) * half ^ 6),
        ((85 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word27Step9 :
    word27Chunk9.foldl (fun acc a => a.applyPacked acc)
      word27State9 = word27State10 := by decide +kernel

private def word27Chunk10 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word27State11 : PackedMat2 :=
    ⟨⟨⟨((-127 : Dyadic) * half ^ 8),
        ((23 : Dyadic) * half ^ 8)⟩,
       ⟨((-63 : Dyadic) * half ^ 8),
        ((3 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 8),
        ((-69 : Dyadic) * half ^ 7)⟩,
       ⟨((43 : Dyadic) * half ^ 8),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((35 : Dyadic) * half ^ 8),
        ((69 : Dyadic) * half ^ 7)⟩,
       ⟨((43 : Dyadic) * half ^ 8),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-127 : Dyadic) * half ^ 8),
        ((23 : Dyadic) * half ^ 8)⟩,
       ⟨((63 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word27Step10 :
    word27Chunk10.foldl (fun acc a => a.applyPacked acc)
      word27State10 = word27State11 := by decide +kernel

private def word27Chunk11 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word27State12 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 6),
        ((119 : Dyadic) * half ^ 9)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-49 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-63 : Dyadic) * half ^ 8),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((-39 : Dyadic) * half ^ 6),
        ((77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-63 : Dyadic) * half ^ 8),
        ((-25 : Dyadic) * half ^ 6)⟩,
       ⟨((39 : Dyadic) * half ^ 6),
        ((-77 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 6),
        ((-119 : Dyadic) * half ^ 9)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-49 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word27Step11 :
    word27Chunk11.foldl (fun acc a => a.applyPacked acc)
      word27State11 = word27State12 := by decide +kernel

private def word27Chunk12 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word27State13 : PackedMat2 :=
    ⟨⟨⟨((281 : Dyadic) * half ^ 10),
        ((373 : Dyadic) * half ^ 10)⟩,
       ⟨((137 : Dyadic) * half ^ 10),
        ((53 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-67 : Dyadic) * half ^ 10),
        ((-135 : Dyadic) * half ^ 10)⟩,
       ⟨((245 : Dyadic) * half ^ 10),
        ((-131 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-389 : Dyadic) * half ^ 10),
        ((39 : Dyadic) * half ^ 8)⟩,
       ⟨((-659 : Dyadic) * half ^ 10),
        ((89 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((267 : Dyadic) * half ^ 10),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((-479 : Dyadic) * half ^ 10),
        ((-209 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word27Step12 :
    word27Chunk12.foldl (fun acc a => a.applyPacked acc)
      word27State12 = word27State13 := by decide +kernel

private def word27Chunk13 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word27State14 : PackedMat2 :=
    ⟨⟨⟨((271 : Dyadic) * half ^ 10),
        ((5 : Dyadic) * half ^ 8)⟩,
       ⟨((31 : Dyadic) * half ^ 8),
        ((517 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-199 : Dyadic) * half ^ 9),
        ((21 : Dyadic) * half ^ 9)⟩,
       ⟨((-489 : Dyadic) * half ^ 10),
        ((27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((489 : Dyadic) * half ^ 10),
        ((-27 : Dyadic) * half ^ 8)⟩,
       ⟨((199 : Dyadic) * half ^ 9),
        ((-21 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 8),
        ((517 : Dyadic) * half ^ 10)⟩,
       ⟨((271 : Dyadic) * half ^ 10),
        ((5 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word27Step13 :
    word27Chunk13.foldl (fun acc a => a.applyPacked acc)
      word27State13 = word27State14 := by decide +kernel

private def word27Chunk14 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word27State15 : PackedMat2 :=
    ⟨⟨⟨((-879 : Dyadic) * half ^ 11),
        ((983 : Dyadic) * half ^ 12)⟩,
       ⟨((885 : Dyadic) * half ^ 11),
        ((1411 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-87 : Dyadic) * half ^ 10),
        ((1351 : Dyadic) * half ^ 12)⟩,
       ⟨((91 : Dyadic) * half ^ 9),
        ((-411 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 9),
        ((-411 : Dyadic) * half ^ 12)⟩,
       ⟨((-87 : Dyadic) * half ^ 10),
        ((1351 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-885 : Dyadic) * half ^ 11),
        ((-1411 : Dyadic) * half ^ 12)⟩,
       ⟨((879 : Dyadic) * half ^ 11),
        ((-983 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word27Step14 :
    word27Chunk14.foldl (fun acc a => a.applyPacked acc)
      word27State14 = word27State15 := by decide +kernel

private def word27Chunk15 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word27State16 : PackedMat2 :=
    ⟨⟨⟨((71 : Dyadic) * half ^ 9),
        ((-2979 : Dyadic) * half ^ 13)⟩,
       ⟨((1413 : Dyadic) * half ^ 12),
        ((2215 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-105 : Dyadic) * half ^ 11),
        ((57 : Dyadic) * half ^ 13)⟩,
       ⟨((-371 : Dyadic) * half ^ 12),
        ((3843 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-975 : Dyadic) * half ^ 11),
        ((581 : Dyadic) * half ^ 13)⟩,
       ⟨((1893 : Dyadic) * half ^ 12),
        ((-161 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-191 : Dyadic) * half ^ 11),
        ((1981 : Dyadic) * half ^ 13)⟩,
       ⟨((-2597 : Dyadic) * half ^ 12),
        ((-845 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word27Step15 :
    word27Chunk15.foldl (fun acc a => a.applyPacked acc)
      word27State15 = word27State16 := by decide +kernel

private def word27Chunk16 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word27State17 : PackedMat2 :=
    ⟨⟨⟨((-1153 : Dyadic) * half ^ 13),
        ((-2371 : Dyadic) * half ^ 13)⟩,
       ⟨((-2763 : Dyadic) * half ^ 13),
        ((-473 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-131 : Dyadic) * half ^ 13),
        ((2231 : Dyadic) * half ^ 13)⟩,
       ⟨((-1233 : Dyadic) * half ^ 13),
        ((1025 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((1233 : Dyadic) * half ^ 13),
        ((-1025 : Dyadic) * half ^ 11)⟩,
       ⟨((131 : Dyadic) * half ^ 13),
        ((-2231 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-2763 : Dyadic) * half ^ 13),
        ((-473 : Dyadic) * half ^ 12)⟩,
       ⟨((-1153 : Dyadic) * half ^ 13),
        ((-2371 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word27Step16 :
    word27Chunk16.foldl (fun acc a => a.applyPacked acc)
      word27State16 = word27State17 := by decide +kernel

private def word27Chunk17 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word27State18 : PackedMat2 :=
    ⟨⟨⟨((-803 : Dyadic) * half ^ 12),
        ((3893 : Dyadic) * half ^ 14)⟩,
       ⟨((-397 : Dyadic) * half ^ 11),
        ((-2903 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4229 : Dyadic) * half ^ 13),
        ((-3285 : Dyadic) * half ^ 14)⟩,
       ⟨((4611 : Dyadic) * half ^ 13),
        ((3369 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 12),
        ((1105 : Dyadic) * half ^ 11)⟩,
       ⟨((-3327 : Dyadic) * half ^ 13),
        ((-191 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-495 : Dyadic) * half ^ 13),
        ((1597 : Dyadic) * half ^ 13)⟩,
       ⟨((-1699 : Dyadic) * half ^ 12),
        ((9 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word27Step17 :
    word27Chunk17.foldl (fun acc a => a.applyPacked acc)
      word27State17 = word27State18 := by decide +kernel

private def word27Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word27State19 : PackedMat2 :=
    ⟨⟨⟨((3015 : Dyadic) * half ^ 13),
        ((99 : Dyadic) * half ^ 9)⟩,
       ⟨((575 : Dyadic) * half ^ 14),
        ((-2017 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-941 : Dyadic) * half ^ 14),
        ((-15 : Dyadic) * half ^ 7)⟩,
       ⟨((-713 : Dyadic) * half ^ 12),
        ((5705 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-3785 : Dyadic) * half ^ 14),
        ((3793 : Dyadic) * half ^ 15)⟩,
       ⟨((7625 : Dyadic) * half ^ 14),
        ((-1911 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1225 : Dyadic) * half ^ 12),
        ((6605 : Dyadic) * half ^ 15)⟩,
       ⟨((2809 : Dyadic) * half ^ 12),
        ((5455 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word27Step18 :
    word27Chunk18.foldl (fun acc a => a.applyPacked acc)
      word27State18 = word27State19 := by decide +kernel

private def word27Chunk19 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word27State20 : PackedMat2 :=
    ⟨⟨⟨((709 : Dyadic) * half ^ 13),
        ((-6455 : Dyadic) * half ^ 16)⟩,
       ⟨((5941 : Dyadic) * half ^ 14),
        ((-9961 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-23297 : Dyadic) * half ^ 15),
        ((2581 : Dyadic) * half ^ 16)⟩,
       ⟨((14831 : Dyadic) * half ^ 15),
        ((13269 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((14831 : Dyadic) * half ^ 15),
        ((13269 : Dyadic) * half ^ 16)⟩,
       ⟨((-23297 : Dyadic) * half ^ 15),
        ((2581 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-5941 : Dyadic) * half ^ 14),
        ((9961 : Dyadic) * half ^ 16)⟩,
       ⟨((-709 : Dyadic) * half ^ 13),
        ((6455 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word27Step19 :
    word27Chunk19.foldl (fun acc a => a.applyPacked acc)
      word27State19 = word27State20 := by decide +kernel

private def word27Chunk20 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word27State21 : PackedMat2 :=
    ⟨⟨⟨((39791 : Dyadic) * half ^ 16),
        ((-8961 : Dyadic) * half ^ 17)⟩,
       ⟨((-9855 : Dyadic) * half ^ 16),
        ((429 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-7877 : Dyadic) * half ^ 15),
        ((-55163 : Dyadic) * half ^ 17)⟩,
       ⟨((6037 : Dyadic) * half ^ 14),
        ((-21047 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-6037 : Dyadic) * half ^ 14),
        ((21047 : Dyadic) * half ^ 17)⟩,
       ⟨((7877 : Dyadic) * half ^ 15),
        ((55163 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-9855 : Dyadic) * half ^ 16),
        ((429 : Dyadic) * half ^ 17)⟩,
       ⟨((39791 : Dyadic) * half ^ 16),
        ((-8961 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word27Step20 :
    word27Chunk20.foldl (fun acc a => a.applyPacked acc)
      word27State20 = word27State21 := by decide +kernel

private def word27Chunk21 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word27State22 : PackedMat2 :=
    ⟨⟨⟨((-37211 : Dyadic) * half ^ 17),
        ((87547 : Dyadic) * half ^ 18)⟩,
       ⟨((11581 : Dyadic) * half ^ 16),
        ((-68573 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-75045 : Dyadic) * half ^ 17),
        ((-40397 : Dyadic) * half ^ 18)⟩,
       ⟨((-16053 : Dyadic) * half ^ 16),
        ((-56513 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-48455 : Dyadic) * half ^ 17),
        ((-107151 : Dyadic) * half ^ 18)⟩,
       ⟨((4029 : Dyadic) * half ^ 16),
        ((-42939 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-9487 : Dyadic) * half ^ 17),
        ((14049 : Dyadic) * half ^ 18)⟩,
       ⟨((-19515 : Dyadic) * half ^ 15),
        ((60373 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word27Step21 :
    word27Chunk21.foldl (fun acc a => a.applyPacked acc)
      word27State21 = word27State22 := by decide +kernel

private def word27Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word27State23 : PackedMat2 :=
    ⟨⟨⟨((-921 : Dyadic) * half ^ 12),
        ((92505 : Dyadic) * half ^ 18)⟩,
       ⟨((-35141 : Dyadic) * half ^ 16),
        ((-6951 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-6667 : Dyadic) * half ^ 17),
        ((-9463 : Dyadic) * half ^ 15)⟩,
       ⟨((-15587 : Dyadic) * half ^ 15),
        ((-19961 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((55743 : Dyadic) * half ^ 18),
        ((-55681 : Dyadic) * half ^ 18)⟩,
       ⟨((-95665 : Dyadic) * half ^ 18),
        ((-69015 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((106407 : Dyadic) * half ^ 18),
        ((20405 : Dyadic) * half ^ 17)⟩,
       ⟨((-78603 : Dyadic) * half ^ 18),
        ((49877 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word27Step22 :
    word27Chunk22.foldl (fun acc a => a.applyPacked acc)
      word27State22 = word27State23 := by decide +kernel

private def word27Chunk23 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word27State24 : PackedMat2 :=
    ⟨⟨⟨((22411 : Dyadic) * half ^ 18),
        ((201475 : Dyadic) * half ^ 19)⟩,
       ⟨((-139599 : Dyadic) * half ^ 18),
        ((4283 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-2943 : Dyadic) * half ^ 16),
        ((17089 : Dyadic) * half ^ 17)⟩,
       ⟨((-160555 : Dyadic) * half ^ 18),
        ((8215 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-2943 : Dyadic) * half ^ 16),
        ((17089 : Dyadic) * half ^ 17)⟩,
       ⟨((160555 : Dyadic) * half ^ 18),
        ((-8215 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-22411 : Dyadic) * half ^ 18),
        ((-201475 : Dyadic) * half ^ 19)⟩,
       ⟨((-139599 : Dyadic) * half ^ 18),
        ((4283 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word27Step23 :
    word27Chunk23.foldl (fun acc a => a.applyPacked acc)
      word27State23 = word27State24 := by decide +kernel

private def word27Chunk24 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word27State25 : PackedMat2 :=
    ⟨⟨⟨((622007 : Dyadic) * half ^ 20),
        ((-121093 : Dyadic) * half ^ 20)⟩,
       ⟨((155657 : Dyadic) * half ^ 20),
        ((-125025 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((642165 : Dyadic) * half ^ 20),
        ((130251 : Dyadic) * half ^ 20)⟩,
       ⟨((-225721 : Dyadic) * half ^ 20),
        ((-67783 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-265817 : Dyadic) * half ^ 20),
        ((-433943 : Dyadic) * half ^ 20)⟩,
       ⟨((-5315 : Dyadic) * half ^ 20),
        ((104111 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((128957 : Dyadic) * half ^ 20),
        ((233175 : Dyadic) * half ^ 20)⟩,
       ⟨((371143 : Dyadic) * half ^ 20),
        ((-12151 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word27Step24 :
    word27Chunk24.foldl (fun acc a => a.applyPacked acc)
      word27State24 = word27State25 := by decide +kernel

private def word27Chunk25 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word27State26 : PackedMat2 :=
    ⟨⟨⟨((5641 : Dyadic) * half ^ 15),
        ((237933 : Dyadic) * half ^ 19)⟩,
       ⟨((327011 : Dyadic) * half ^ 20),
        ((-203135 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((366807 : Dyadic) * half ^ 20),
        ((7527 : Dyadic) * half ^ 16)⟩,
       ⟨((-55129 : Dyadic) * half ^ 19),
        ((-25213 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((55129 : Dyadic) * half ^ 19),
        ((25213 : Dyadic) * half ^ 20)⟩,
       ⟨((-366807 : Dyadic) * half ^ 20),
        ((-7527 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((327011 : Dyadic) * half ^ 20),
        ((-203135 : Dyadic) * half ^ 19)⟩,
       ⟨((5641 : Dyadic) * half ^ 15),
        ((237933 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word27Step25 :
    word27Chunk25.foldl (fun acc a => a.applyPacked acc)
      word27State25 = word27State26 := by decide +kernel

private def word27Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word27State27 : PackedMat2 :=
    ⟨⟨⟨((1805913 : Dyadic) * half ^ 21),
        ((-148011 : Dyadic) * half ^ 22)⟩,
       ⟨((370005 : Dyadic) * half ^ 21),
        ((-656127 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1059 : Dyadic) * half ^ 16),
        ((127417 : Dyadic) * half ^ 22)⟩,
       ⟨((353373 : Dyadic) * half ^ 20),
        ((727819 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((353373 : Dyadic) * half ^ 20),
        ((727819 : Dyadic) * half ^ 22)⟩,
       ⟨((-1059 : Dyadic) * half ^ 16),
        ((127417 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-370005 : Dyadic) * half ^ 21),
        ((656127 : Dyadic) * half ^ 22)⟩,
       ⟨((-1805913 : Dyadic) * half ^ 21),
        ((148011 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word27Step26 :
    word27Chunk26.foldl (fun acc a => a.applyPacked acc)
      word27State26 = word27State27 := by decide +kernel

private def word27Chunk27 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word27State28 : PackedMat2 :=
    ⟨⟨⟨((327093 : Dyadic) * half ^ 22),
        ((1956215 : Dyadic) * half ^ 23)⟩,
       ⟨((488937 : Dyadic) * half ^ 20),
        ((-2367463 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((56989 : Dyadic) * half ^ 22),
        ((-583671 : Dyadic) * half ^ 23)⟩,
       ⟨((694743 : Dyadic) * half ^ 20),
        ((1447859 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-56989 : Dyadic) * half ^ 22),
        ((583671 : Dyadic) * half ^ 23)⟩,
       ⟨((694743 : Dyadic) * half ^ 20),
        ((1447859 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((327093 : Dyadic) * half ^ 22),
        ((1956215 : Dyadic) * half ^ 23)⟩,
       ⟨((-488937 : Dyadic) * half ^ 20),
        ((2367463 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word27Step27 :
    word27Chunk27.foldl (fun acc a => a.applyPacked acc)
      word27State27 = word27State28 := by decide +kernel

private def word27Chunk28 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word27State29 : PackedMat2 :=
    ⟨⟨⟨((3545885 : Dyadic) * half ^ 23),
        ((-4038557 : Dyadic) * half ^ 24)⟩,
       ⟨((2475055 : Dyadic) * half ^ 22),
        ((4098303 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((652207 : Dyadic) * half ^ 23),
        ((2424895 : Dyadic) * half ^ 24)⟩,
       ⟨((1636653 : Dyadic) * half ^ 22),
        ((-2306025 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((59435 : Dyadic) * half ^ 23),
        ((3925513 : Dyadic) * half ^ 24)⟩,
       ⟨((591365 : Dyadic) * half ^ 21),
        ((-2621099 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-29873 : Dyadic) * half ^ 23),
        ((-8495995 : Dyadic) * half ^ 24)⟩,
       ⟨((2034215 : Dyadic) * half ^ 22),
        ((1404225 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word27Step28 :
    word27Chunk28.foldl (fun acc a => a.applyPacked acc)
      word27State28 = word27State29 := by decide +kernel

private def word27Chunk29 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word27State30 : PackedMat2 :=
    ⟨⟨⟨((498345 : Dyadic) * half ^ 24),
        ((-3084587 : Dyadic) * half ^ 23)⟩,
       ⟨((4214421 : Dyadic) * half ^ 24),
        ((2156783 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((70227 : Dyadic) * half ^ 24),
        ((-867925 : Dyadic) * half ^ 22)⟩,
       ⟨((658783 : Dyadic) * half ^ 24),
        ((-8760711 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((658783 : Dyadic) * half ^ 24),
        ((-8760711 : Dyadic) * half ^ 24)⟩,
       ⟨((70227 : Dyadic) * half ^ 24),
        ((-867925 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-4214421 : Dyadic) * half ^ 24),
        ((-2156783 : Dyadic) * half ^ 24)⟩,
       ⟨((-498345 : Dyadic) * half ^ 24),
        ((3084587 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word27Step29 :
    word27Chunk29.foldl (fun acc a => a.applyPacked acc)
      word27State29 = word27State30 := by decide +kernel

private def word27Chunk30 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word27State31 : PackedMat2 :=
    ⟨⟨⟨((-16522563 : Dyadic) * half ^ 25),
        ((-5879129 : Dyadic) * half ^ 24)⟩,
       ⟨((-12089505 : Dyadic) * half ^ 25),
        ((9448153 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((9901061 : Dyadic) * half ^ 25),
        ((-3420445 : Dyadic) * half ^ 24)⟩,
       ⟨((-7382621 : Dyadic) * half ^ 25),
        ((1668919 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((7382621 : Dyadic) * half ^ 25),
        ((-1668919 : Dyadic) * half ^ 25)⟩,
       ⟨((-9901061 : Dyadic) * half ^ 25),
        ((3420445 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-12089505 : Dyadic) * half ^ 25),
        ((9448153 : Dyadic) * half ^ 25)⟩,
       ⟨((-16522563 : Dyadic) * half ^ 25),
        ((-5879129 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word27Step30 :
    word27Chunk30.foldl (fun acc a => a.applyPacked acc)
      word27State30 = word27State31 := by decide +kernel

private def word27Chunk31 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word27State32 : PackedMat2 :=
    ⟨⟨⟨((-36287355 : Dyadic) * half ^ 26),
        ((-8780195 : Dyadic) * half ^ 26)⟩,
       ⟨((-48464557 : Dyadic) * half ^ 26),
        ((3989017 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((14326207 : Dyadic) * half ^ 26),
        ((-298255 : Dyadic) * half ^ 26)⟩,
       ⟨((-5732667 : Dyadic) * half ^ 26),
        ((-6307247 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-12316239 : Dyadic) * half ^ 26),
        ((-10029437 : Dyadic) * half ^ 26)⟩,
       ⟨((-12912749 : Dyadic) * half ^ 26),
        ((2148385 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-16758229 : Dyadic) * half ^ 26),
        ((6088601 : Dyadic) * half ^ 26)⟩,
       ⟨((802161 : Dyadic) * half ^ 26),
        ((10593989 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word27Step31 :
    word27Chunk31.foldl (fun acc a => a.applyPacked acc)
      word27State31 = word27State32 := by decide +kernel

private def word27Chunk32 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word27State33 : PackedMat2 :=
    ⟨⟨⟨((18318417 : Dyadic) * half ^ 26),
        ((-31650895 : Dyadic) * half ^ 27)⟩,
       ⟨((-17328747 : Dyadic) * half ^ 26),
        ((-56946497 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-2708025 : Dyadic) * half ^ 23),
        ((34918735 : Dyadic) * half ^ 27)⟩,
       ⟨((-5898767 : Dyadic) * half ^ 24),
        ((-14811117 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((5898767 : Dyadic) * half ^ 24),
        ((14811117 : Dyadic) * half ^ 27)⟩,
       ⟨((2708025 : Dyadic) * half ^ 23),
        ((-34918735 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-17328747 : Dyadic) * half ^ 26),
        ((-56946497 : Dyadic) * half ^ 27)⟩,
       ⟨((18318417 : Dyadic) * half ^ 26),
        ((-31650895 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word27Step32 :
    word27Chunk32.foldl (fun acc a => a.applyPacked acc)
      word27State32 = word27State33 := by decide +kernel

private def word27Chunk33 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word27State34 : PackedMat2 :=
    ⟨⟨⟨((35253199 : Dyadic) * half ^ 27),
        ((139055673 : Dyadic) * half ^ 28)⟩,
       ⟨((3253167 : Dyadic) * half ^ 25),
        ((-8633463 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((52795447 : Dyadic) * half ^ 27),
        ((-75123247 : Dyadic) * half ^ 28)⟩,
       ⟨((15151547 : Dyadic) * half ^ 26),
        ((-27180311 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-51151779 : Dyadic) * half ^ 27),
        ((83098541 : Dyadic) * half ^ 28)⟩,
       ⟨((-5992867 : Dyadic) * half ^ 25),
        ((22492353 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-65211105 : Dyadic) * half ^ 27),
        ((-48265867 : Dyadic) * half ^ 28)⟩,
       ⟨((-9230571 : Dyadic) * half ^ 24),
        ((-22240531 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word27Step33 :
    word27Chunk33.foldl (fun acc a => a.applyPacked acc)
      word27State33 = word27State34 := by decide +kernel

private def word27Chunk34 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word27State35 : PackedMat2 :=
    ⟨⟨⟨((156346099 : Dyadic) * half ^ 28),
        ((25979775 : Dyadic) * half ^ 28)⟩,
       ⟨((79415183 : Dyadic) * half ^ 28),
        ((44978881 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-118439009 : Dyadic) * half ^ 28),
        ((35351167 : Dyadic) * half ^ 27)⟩,
       ⟨((-9638063 : Dyadic) * half ^ 28),
        ((-38393183 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((118439009 : Dyadic) * half ^ 28),
        ((-35351167 : Dyadic) * half ^ 27)⟩,
       ⟨((-9638063 : Dyadic) * half ^ 28),
        ((-38393183 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((156346099 : Dyadic) * half ^ 28),
        ((25979775 : Dyadic) * half ^ 28)⟩,
       ⟨((-79415183 : Dyadic) * half ^ 28),
        ((-44978881 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word27Step34 :
    word27Chunk34.foldl (fun acc a => a.applyPacked acc)
      word27State34 = word27State35 := by decide +kernel

private def word27Chunk35 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word27State36 : PackedMat2 :=
    ⟨⟨⟨((5904857 : Dyadic) * half ^ 26),
        ((96498715 : Dyadic) * half ^ 29)⟩,
       ⟨((4510885 : Dyadic) * half ^ 26),
        ((63494931 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((152048473 : Dyadic) * half ^ 28),
        ((7628615 : Dyadic) * half ^ 26)⟩,
       ⟨((14063169 : Dyadic) * half ^ 26),
        ((-246209535 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((152048473 : Dyadic) * half ^ 28),
        ((7628615 : Dyadic) * half ^ 26)⟩,
       ⟨((-14063169 : Dyadic) * half ^ 26),
        ((246209535 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-5904857 : Dyadic) * half ^ 26),
        ((-96498715 : Dyadic) * half ^ 29)⟩,
       ⟨((4510885 : Dyadic) * half ^ 26),
        ((63494931 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word27Step35 :
    word27Chunk35.foldl (fun acc a => a.applyPacked acc)
      word27State35 = word27State36 := by decide +kernel

private def word27Chunk36 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word27State37 : PackedMat2 :=
    ⟨⟨⟨((-46372853 : Dyadic) * half ^ 27),
        ((-287169585 : Dyadic) * half ^ 30)⟩,
       ⟨((15564033 : Dyadic) * half ^ 27),
        ((401895819 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((211349667 : Dyadic) * half ^ 29),
        ((-268686203 : Dyadic) * half ^ 30)⟩,
       ⟨((74508187 : Dyadic) * half ^ 29),
        ((-288575421 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-69657703 : Dyadic) * half ^ 27),
        ((142928927 : Dyadic) * half ^ 29)⟩,
       ⟨((9944609 : Dyadic) * half ^ 29),
        ((17105185 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-57363117 : Dyadic) * half ^ 29),
        ((7702205 : Dyadic) * half ^ 26)⟩,
       ⟨((172266351 : Dyadic) * half ^ 28),
        ((30968443 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word27Step36 :
    word27Chunk36.foldl (fun acc a => a.applyPacked acc)
      word27State36 = word27State37 := by decide +kernel

private def word27Chunk37 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word27State38 : PackedMat2 :=
    ⟨⟨⟨((-299256213 : Dyadic) * half ^ 29),
        ((-39990213 : Dyadic) * half ^ 28)⟩,
       ⟨((250360547 : Dyadic) * half ^ 30),
        ((-449337 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((502363679 : Dyadic) * half ^ 30),
        ((-11021153 : Dyadic) * half ^ 28)⟩,
       ⟨((-39143243 : Dyadic) * half ^ 28),
        ((447025873 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((39143243 : Dyadic) * half ^ 28),
        ((-447025873 : Dyadic) * half ^ 30)⟩,
       ⟨((-502363679 : Dyadic) * half ^ 30),
        ((11021153 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((250360547 : Dyadic) * half ^ 30),
        ((-449337 : Dyadic) * half ^ 25)⟩,
       ⟨((-299256213 : Dyadic) * half ^ 29),
        ((-39990213 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word27Step37 :
    word27Chunk37.foldl (fun acc a => a.applyPacked acc)
      word27State37 = word27State38 := by decide +kernel

private def word27Chunk38 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word27State39 : PackedMat2 :=
    ⟨⟨⟨((-33168523 : Dyadic) * half ^ 26),
        ((-509330633 : Dyadic) * half ^ 32)⟩,
       ⟨((-1030211255 : Dyadic) * half ^ 31),
        ((-164991317 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((26748227 : Dyadic) * half ^ 28),
        ((959548585 : Dyadic) * half ^ 32)⟩,
       ⟨((1222075789 : Dyadic) * half ^ 31),
        ((-749467047 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((26748227 : Dyadic) * half ^ 28),
        ((959548585 : Dyadic) * half ^ 32)⟩,
       ⟨((-1222075789 : Dyadic) * half ^ 31),
        ((749467047 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((33168523 : Dyadic) * half ^ 26),
        ((509330633 : Dyadic) * half ^ 32)⟩,
       ⟨((-1030211255 : Dyadic) * half ^ 31),
        ((-164991317 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word27Step38 :
    word27Chunk38.foldl (fun acc a => a.applyPacked acc)
      word27State38 = word27State39 := by decide +kernel

private def word27Chunk39 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word27State40 : PackedMat2 :=
    ⟨⟨⟨((2773942149 : Dyadic) * half ^ 32),
        ((-89099 : Dyadic) * half ^ 21)⟩,
       ⟨((-473383225 : Dyadic) * half ^ 32),
        ((-242000307 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-409384131 : Dyadic) * half ^ 32),
        ((-593495015 : Dyadic) * half ^ 32)⟩,
       ⟨((-1240210179 : Dyadic) * half ^ 32),
        ((526736623 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((560115819 : Dyadic) * half ^ 31),
        ((-12981657 : Dyadic) * half ^ 27)⟩,
       ⟨((-8344799 : Dyadic) * half ^ 29),
        ((-824797155 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((219190963 : Dyadic) * half ^ 29),
        ((1623662687 : Dyadic) * half ^ 32)⟩,
       ⟨((264809651 : Dyadic) * half ^ 29),
        ((-575139731 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word27Step39 :
    word27Chunk39.foldl (fun acc a => a.applyPacked acc)
      word27State39 = word27State40 := by decide +kernel

private def word27Chunk40 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word27State41 : PackedMat2 :=
    ⟨⟨⟨((4951133221 : Dyadic) * half ^ 33),
        ((741126425 : Dyadic) * half ^ 33)⟩,
       ⟨((-5342906817 : Dyadic) * half ^ 33),
        ((1422415423 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1087899727 : Dyadic) * half ^ 33),
        ((1057797191 : Dyadic) * half ^ 32)⟩,
       ⟨((-2043471141 : Dyadic) * half ^ 33),
        ((-49819117 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1456350127 : Dyadic) * half ^ 32),
        ((782842717 : Dyadic) * half ^ 32)⟩,
       ⟨((-659244255 : Dyadic) * half ^ 32),
        ((477785707 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((340644499 : Dyadic) * half ^ 32),
        ((-5147020019 : Dyadic) * half ^ 33)⟩,
       ⟨((270442731 : Dyadic) * half ^ 30),
        ((-97943399 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word27Step40 :
    word27Chunk40.foldl (fun acc a => a.applyPacked acc)
      word27State40 = word27State41 := by decide +kernel

private def word27Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word27State42 : PackedMat2 :=
    ⟨⟨⟨((3912459413 : Dyadic) * half ^ 34),
        ((490758091 : Dyadic) * half ^ 32)⟩,
       ⟨((9114452577 : Dyadic) * half ^ 34),
        ((-5079566099 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5593370907 : Dyadic) * half ^ 34),
        ((3516012809 : Dyadic) * half ^ 33)⟩,
       ⟨((-2669853865 : Dyadic) * half ^ 34),
        ((268010039 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-2669853865 : Dyadic) * half ^ 34),
        ((268010039 : Dyadic) * half ^ 34)⟩,
       ⟨((5593370907 : Dyadic) * half ^ 34),
        ((3516012809 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-9114452577 : Dyadic) * half ^ 34),
        ((5079566099 : Dyadic) * half ^ 34)⟩,
       ⟨((-3912459413 : Dyadic) * half ^ 34),
        ((-490758091 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word27Step41 :
    word27Chunk41.foldl (fun acc a => a.applyPacked acc)
      word27State41 = word27State42 := by decide +kernel

private def word27Chunk42 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word27State43 : PackedMat2 :=
    ⟨⟨⟨((-2240469775 : Dyadic) * half ^ 35),
        ((-1503272045 : Dyadic) * half ^ 32)⟩,
       ⟨((11887168413 : Dyadic) * half ^ 35),
        ((7782046989 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-8558668313 : Dyadic) * half ^ 35),
        ((7771019899 : Dyadic) * half ^ 34)⟩,
       ⟨((-2445936077 : Dyadic) * half ^ 35),
        ((-5547314121 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((21089353919 : Dyadic) * half ^ 35),
        ((-1528183059 : Dyadic) * half ^ 34)⟩,
       ⟨((-9994725677 : Dyadic) * half ^ 35),
        ((5502302195 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((19808223349 : Dyadic) * half ^ 35),
        ((3531909547 : Dyadic) * half ^ 34)⟩,
       ⟨((-4244129371 : Dyadic) * half ^ 35),
        ((4823349319 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word27Step42 :
    word27Chunk42.foldl (fun acc a => a.applyPacked acc)
      word27State42 = word27State43 := by decide +kernel

private def word27Chunk43 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word27State44 : PackedMat2 :=
    ⟨⟨⟨((-19730560739 : Dyadic) * half ^ 35),
        ((-1491063489 : Dyadic) * half ^ 33)⟩,
       ⟨((2465602979 : Dyadic) * half ^ 32),
        ((-335326559 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-3981557477 : Dyadic) * half ^ 34),
        ((4261616315 : Dyadic) * half ^ 35)⟩,
       ⟨((-13924914469 : Dyadic) * half ^ 35),
        ((2056935619 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((8375487553 : Dyadic) * half ^ 35),
        ((-21888029423 : Dyadic) * half ^ 36)⟩,
       ⟨((147745077 : Dyadic) * half ^ 35),
        ((5961799515 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((57074689 : Dyadic) * half ^ 28),
        ((5736907 : Dyadic) * half ^ 36)⟩,
       ⟨((577868465 : Dyadic) * half ^ 32),
        ((39455384571 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word27Step43 :
    word27Chunk43.foldl (fun acc a => a.applyPacked acc)
      word27State43 = word27State44 := by decide +kernel

private def word27Chunk44 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word27State45 : PackedMat2 :=
    ⟨⟨⟨((-12580325767 : Dyadic) * half ^ 36),
        ((-16321031557 : Dyadic) * half ^ 37)⟩,
       ⟨((-16418015147 : Dyadic) * half ^ 35),
        ((-17479374823 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((41766335239 : Dyadic) * half ^ 36),
        ((1139332321 : Dyadic) * half ^ 37)⟩,
       ⟨((8515527725 : Dyadic) * half ^ 34),
        ((-24275151741 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((5783954855 : Dyadic) * half ^ 35),
        ((-75828446139 : Dyadic) * half ^ 37)⟩,
       ⟨((-12707242031 : Dyadic) * half ^ 36),
        ((-7704224339 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-8450101595 : Dyadic) * half ^ 35),
        ((-45416356061 : Dyadic) * half ^ 37)⟩,
       ⟨((579171633 : Dyadic) * half ^ 36),
        ((20255704527 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word27Step44 :
    word27Chunk44.foldl (fun acc a => a.applyPacked acc)
      word27State44 = word27State45 := by decide +kernel

private def word27Chunk45 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word27State46 : PackedMat2 :=
    ⟨⟨⟨((50577109637 : Dyadic) * half ^ 37),
        ((-7989107113 : Dyadic) * half ^ 36)⟩,
       ⟨((11706634649 : Dyadic) * half ^ 37),
        ((-5053359989 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-86748285 : Dyadic) * half ^ 37),
        ((62643598521 : Dyadic) * half ^ 37)⟩,
       ⟨((30071509265 : Dyadic) * half ^ 37),
        ((42792292839 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((9925652841 : Dyadic) * half ^ 36),
        ((-15079128775 : Dyadic) * half ^ 37)⟩,
       ⟨((-3294871605 : Dyadic) * half ^ 32),
        ((-7496190245 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-12224332843 : Dyadic) * half ^ 36),
        ((-9717618747 : Dyadic) * half ^ 36)⟩,
       ⟨((-28202547069 : Dyadic) * half ^ 36),
        ((31141872143 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word27Step45 :
    word27Chunk45.foldl (fun acc a => a.applyPacked acc)
      word27State45 = word27State46 := by decide +kernel

private def word27Chunk46 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word27State47 : PackedMat2 :=
    ⟨⟨⟨((41319657347 : Dyadic) * half ^ 37),
        ((7018748085 : Dyadic) * half ^ 36)⟩,
       ⟨((-25426217365 : Dyadic) * half ^ 37),
        ((-33371845179 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-64763460977 : Dyadic) * half ^ 37),
        ((91589361123 : Dyadic) * half ^ 38)⟩,
       ⟨((18073509139 : Dyadic) * half ^ 36),
        ((6783192897 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((64763460977 : Dyadic) * half ^ 37),
        ((-91589361123 : Dyadic) * half ^ 38)⟩,
       ⟨((18073509139 : Dyadic) * half ^ 36),
        ((6783192897 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((41319657347 : Dyadic) * half ^ 37),
        ((7018748085 : Dyadic) * half ^ 36)⟩,
       ⟨((25426217365 : Dyadic) * half ^ 37),
        ((33371845179 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word27Step46 :
    word27Chunk46.foldl (fun acc a => a.applyPacked acc)
      word27State46 = word27State47 := by decide +kernel

private def word27Chunk47 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word27State48 : PackedMat2 :=
    ⟨⟨⟨((-93118028065 : Dyadic) * half ^ 39),
        ((36156900643 : Dyadic) * half ^ 37)⟩,
       ⟨((32837349565 : Dyadic) * half ^ 39),
        ((78133036865 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((105587832851 : Dyadic) * half ^ 39),
        ((-55541142081 : Dyadic) * half ^ 37)⟩,
       ⟨((148982088269 : Dyadic) * half ^ 39),
        ((230629272391 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-452793840715 : Dyadic) * half ^ 39),
        ((-21697127709 : Dyadic) * half ^ 39)⟩,
       ⟨((-8464704067 : Dyadic) * half ^ 39),
        ((-7955310035 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-66494565707 : Dyadic) * half ^ 39),
        ((62977688815 : Dyadic) * half ^ 39)⟩,
       ⟨((222760639437 : Dyadic) * half ^ 39),
        ((-15070169625 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word27Step47 :
    word27Chunk47.foldl (fun acc a => a.applyPacked acc)
      word27State47 = word27State48 := by decide +kernel

private def word27Chunk48 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word27State49 : PackedMat2 :=
    ⟨⟨⟨((181002844215 : Dyadic) * half ^ 39),
        ((-196707816627 : Dyadic) * half ^ 39)⟩,
       ⟨((-21458510651 : Dyadic) * half ^ 38),
        ((-26582160127 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-125048299213 : Dyadic) * half ^ 38),
        ((-4213578783 : Dyadic) * half ^ 34)⟩,
       ⟨((299841863599 : Dyadic) * half ^ 39),
        ((2475278405 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((299841863599 : Dyadic) * half ^ 39),
        ((2475278405 : Dyadic) * half ^ 39)⟩,
       ⟨((-125048299213 : Dyadic) * half ^ 38),
        ((-4213578783 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((21458510651 : Dyadic) * half ^ 38),
        ((26582160127 : Dyadic) * half ^ 39)⟩,
       ⟨((-181002844215 : Dyadic) * half ^ 39),
        ((196707816627 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word27Step48 :
    word27Chunk48.foldl (fun acc a => a.applyPacked acc)
      word27State48 = word27State49 := by decide +kernel

private def word27Chunk49 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word27State50 : PackedMat2 :=
    ⟨⟨⟨((-4184807907 : Dyadic) * half ^ 39),
        ((675450375835 : Dyadic) * half ^ 41)⟩,
       ⟨((-249466709663 : Dyadic) * half ^ 40),
        ((-471834532199 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-36034510833 : Dyadic) * half ^ 38),
        ((-232055656469 : Dyadic) * half ^ 41)⟩,
       ⟨((-863300548891 : Dyadic) * half ^ 40),
        ((168541299505 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((15878589241 : Dyadic) * half ^ 39),
        ((1007438592223 : Dyadic) * half ^ 41)⟩,
       ⟨((200298477987 : Dyadic) * half ^ 40),
        ((-719162505559 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((50903960909 : Dyadic) * half ^ 39),
        ((-257836325477 : Dyadic) * half ^ 41)⟩,
       ⟨((573642454017 : Dyadic) * half ^ 40),
        ((241097093849 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word27Step49 :
    word27Chunk49.foldl (fun acc a => a.applyPacked acc)
      word27State49 = word27State50 := by decide +kernel

private def word27Chunk50 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word27State51 : PackedMat2 :=
    ⟨⟨⟨((534527564415 : Dyadic) * half ^ 40),
        ((42946934815 : Dyadic) * half ^ 38)⟩,
       ⟨((-167938087113 : Dyadic) * half ^ 38),
        ((172529128007 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((9732426197 : Dyadic) * half ^ 35),
        ((109316494833 : Dyadic) * half ^ 41)⟩,
       ⟨((68467491459 : Dyadic) * half ^ 39),
        ((-371705555513 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((9732426197 : Dyadic) * half ^ 35),
        ((109316494833 : Dyadic) * half ^ 41)⟩,
       ⟨((-68467491459 : Dyadic) * half ^ 39),
        ((371705555513 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-534527564415 : Dyadic) * half ^ 40),
        ((-42946934815 : Dyadic) * half ^ 38)⟩,
       ⟨((-167938087113 : Dyadic) * half ^ 38),
        ((172529128007 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word27Step50 :
    word27Chunk50.foldl (fun acc a => a.applyPacked acc)
      word27State50 = word27State51 := by decide +kernel

private def word27Chunk51 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word27State52 : PackedMat2 :=
    ⟨⟨⟨((2883383259803 : Dyadic) * half ^ 42),
        ((1071028656209 : Dyadic) * half ^ 42)⟩,
       ⟨((2048208001037 : Dyadic) * half ^ 42),
        ((-724150919803 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-226283326683 : Dyadic) * half ^ 42),
        ((160006474767 : Dyadic) * half ^ 42)⟩,
       ⟨((-347842338917 : Dyadic) * half ^ 42),
        ((30745209579 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((85955201865 : Dyadic) * half ^ 42),
        ((-60779506117 : Dyadic) * half ^ 42)⟩,
       ⟨((405968151399 : Dyadic) * half ^ 42),
        ((-8970713525 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((2519330495815 : Dyadic) * half ^ 42),
        ((417587629383 : Dyadic) * half ^ 42)⟩,
       ⟨((377273183397 : Dyadic) * half ^ 42),
        ((-616448907605 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word27Step51 :
    word27Chunk51.foldl (fun acc a => a.applyPacked acc)
      word27State51 = word27State52 := by decide +kernel

private def word27Chunk52 : List Letter := [.t]
private def word27State53 : PackedMat2 :=
    ⟨⟨⟨((2883383259803 : Dyadic) * half ^ 42),
        ((1071028656209 : Dyadic) * half ^ 42)⟩,
       ⟨((2048208001037 : Dyadic) * half ^ 42),
        ((-724150919803 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-226283326683 : Dyadic) * half ^ 42),
        ((160006474767 : Dyadic) * half ^ 42)⟩,
       ⟨((-347842338917 : Dyadic) * half ^ 42),
        ((30745209579 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((226283326683 : Dyadic) * half ^ 42),
        ((-160006474767 : Dyadic) * half ^ 42)⟩,
       ⟨((-347842338917 : Dyadic) * half ^ 42),
        ((30745209579 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((2883383259803 : Dyadic) * half ^ 42),
        ((1071028656209 : Dyadic) * half ^ 42)⟩,
       ⟨((-2048208001037 : Dyadic) * half ^ 42),
        ((724150919803 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word27Step52 :
    word27Chunk52.foldl (fun acc a => a.applyPacked acc)
      word27State52 = word27State53 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word27_check : check word27 27 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word27 = word27State53.toMatrix := by
    unfold evalRingPacked
    change ((
      word27Chunk0 ++ word27Chunk1 ++ word27Chunk2 ++ word27Chunk3 ++
      word27Chunk4 ++ word27Chunk5 ++ word27Chunk6 ++ word27Chunk7 ++
      word27Chunk8 ++ word27Chunk9 ++ word27Chunk10 ++ word27Chunk11 ++
      word27Chunk12 ++ word27Chunk13 ++ word27Chunk14 ++ word27Chunk15 ++
      word27Chunk16 ++ word27Chunk17 ++ word27Chunk18 ++ word27Chunk19 ++
      word27Chunk20 ++ word27Chunk21 ++ word27Chunk22 ++ word27Chunk23 ++
      word27Chunk24 ++ word27Chunk25 ++ word27Chunk26 ++ word27Chunk27 ++
      word27Chunk28 ++ word27Chunk29 ++ word27Chunk30 ++ word27Chunk31 ++
      word27Chunk32 ++ word27Chunk33 ++ word27Chunk34 ++ word27Chunk35 ++
      word27Chunk36 ++ word27Chunk37 ++ word27Chunk38 ++ word27Chunk39 ++
      word27Chunk40 ++ word27Chunk41 ++ word27Chunk42 ++ word27Chunk43 ++
      word27Chunk44 ++ word27Chunk45 ++ word27Chunk46 ++ word27Chunk47 ++
      word27Chunk48 ++ word27Chunk49 ++ word27Chunk50 ++ word27Chunk51 ++
      word27Chunk52
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word27Step0, word27Step1, word27Step2, word27Step3, word27Step4,
      word27Step5, word27Step6, word27Step7, word27Step8, word27Step9,
      word27Step10, word27Step11, word27Step12, word27Step13, word27Step14,
      word27Step15, word27Step16, word27Step17, word27Step18, word27Step19,
      word27Step20, word27Step21, word27Step22, word27Step23, word27Step24,
      word27Step25, word27Step26, word27Step27, word27Step28, word27Step29,
      word27Step30, word27Step31, word27Step32, word27Step33, word27Step34,
      word27Step35, word27Step36, word27Step37, word27Step38, word27Step39,
      word27Step40, word27Step41, word27Step42, word27Step43, word27Step44,
      word27Step45, word27Step46, word27Step47, word27Step48, word27Step49,
      word27Step50, word27Step51, word27Step52]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
