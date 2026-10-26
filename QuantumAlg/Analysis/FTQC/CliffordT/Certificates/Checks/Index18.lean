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
private def word18Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word18State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word18Step0 :
    word18Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word18State1 := by decide +kernel

private def word18Chunk1 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word18State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word18Step1 :
    word18Chunk1.foldl (fun acc a => a.applyPacked acc)
      word18State1 = word18State2 := by decide +kernel

private def word18Chunk2 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word18State3 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word18Step2 :
    word18Chunk2.foldl (fun acc a => a.applyPacked acc)
      word18State2 = word18State3 := by decide +kernel

private def word18Chunk3 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word18State4 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word18Step3 :
    word18Chunk3.foldl (fun acc a => a.applyPacked acc)
      word18State3 = word18State4 := by decide +kernel

private def word18Chunk4 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word18State5 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-13 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word18Step4 :
    word18Chunk4.foldl (fun acc a => a.applyPacked acc)
      word18State4 = word18State5 := by decide +kernel

private def word18Chunk5 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word18State6 : PackedMat2 :=
    ⟨⟨⟨((-21 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩,
       ⟨((-21 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word18Step5 :
    word18Chunk5.foldl (fun acc a => a.applyPacked acc)
      word18State5 = word18State6 := by decide +kernel

private def word18Chunk6 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word18State7 : PackedMat2 :=
    ⟨⟨⟨((-15 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((47 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((-19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((29 : Dyadic) * half ^ 6),
        ((11 : Dyadic) * half ^ 6)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word18Step6 :
    word18Chunk6.foldl (fun acc a => a.applyPacked acc)
      word18State6 = word18State7 := by decide +kernel

private def word18Chunk7 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State8 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((-13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩,
       ⟨((25 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 6),
        ((13 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word18Step7 :
    word18Chunk7.foldl (fun acc a => a.applyPacked acc)
      word18State7 = word18State8 := by decide +kernel

private def word18Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word18State9 : PackedMat2 :=
    ⟨⟨⟨((-25 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 8)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((39 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 6),
        ((-39 : Dyadic) * half ^ 8)⟩,
       ⟨((43 : Dyadic) * half ^ 7),
        ((111 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 6),
        ((39 : Dyadic) * half ^ 8)⟩,
       ⟨((43 : Dyadic) * half ^ 7),
        ((111 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 8)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word18Step8 :
    word18Chunk8.foldl (fun acc a => a.applyPacked acc)
      word18State8 = word18State9 := by decide +kernel

private def word18Chunk9 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word18State10 : PackedMat2 :=
    ⟨⟨⟨((-17 : Dyadic) * half ^ 6),
        ((-21 : Dyadic) * half ^ 9)⟩,
       ⟨((217 : Dyadic) * half ^ 8),
        ((23 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((77 : Dyadic) * half ^ 8),
        ((-65 : Dyadic) * half ^ 9)⟩,
       ⟨((-7 : Dyadic) * half ^ 7),
        ((101 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 7),
        ((63 : Dyadic) * half ^ 9)⟩,
       ⟨((-83 : Dyadic) * half ^ 8),
        ((91 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 8),
        ((-149 : Dyadic) * half ^ 9)⟩,
       ⟨((11 : Dyadic) * half ^ 7),
        ((285 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word18Step9 :
    word18Chunk9.foldl (fun acc a => a.applyPacked acc)
      word18State9 = word18State10 := by decide +kernel

private def word18Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word18State11 : PackedMat2 :=
    ⟨⟨⟨((-315 : Dyadic) * half ^ 9),
        ((-47 : Dyadic) * half ^ 9)⟩,
       ⟨((-59 : Dyadic) * half ^ 9),
        ((257 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-119 : Dyadic) * half ^ 9),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((-39 : Dyadic) * half ^ 9),
        ((-29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((119 : Dyadic) * half ^ 9),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-39 : Dyadic) * half ^ 9),
        ((-29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-315 : Dyadic) * half ^ 9),
        ((-47 : Dyadic) * half ^ 9)⟩,
       ⟨((59 : Dyadic) * half ^ 9),
        ((-257 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word18Step10 :
    word18Chunk10.foldl (fun acc a => a.applyPacked acc)
      word18State10 = word18State11 := by decide +kernel

private def word18Chunk11 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word18State12 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 10),
        ((-493 : Dyadic) * half ^ 10)⟩,
       ⟨((125 : Dyadic) * half ^ 10),
        ((-33 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((281 : Dyadic) * half ^ 10),
        ((-31 : Dyadic) * half ^ 7)⟩,
       ⟨((-539 : Dyadic) * half ^ 10),
        ((-151 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-97 : Dyadic) * half ^ 10),
        ((205 : Dyadic) * half ^ 9)⟩,
       ⟨((399 : Dyadic) * half ^ 10),
        ((129 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((427 : Dyadic) * half ^ 10),
        ((59 : Dyadic) * half ^ 10)⟩,
       ⟨((-559 : Dyadic) * half ^ 10),
        ((33 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word18Step11 :
    word18Chunk11.foldl (fun acc a => a.applyPacked acc)
      word18State11 = word18State12 := by decide +kernel

private def word18Chunk12 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State13 : PackedMat2 :=
    ⟨⟨⟨((-41 : Dyadic) * half ^ 7),
        ((455 : Dyadic) * half ^ 10)⟩,
       ⟨((-139 : Dyadic) * half ^ 10),
        ((-29 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((147 : Dyadic) * half ^ 9),
        ((217 : Dyadic) * half ^ 9)⟩,
       ⟨((-69 : Dyadic) * half ^ 10),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-69 : Dyadic) * half ^ 10),
        ((-5 : Dyadic) * half ^ 6)⟩,
       ⟨((147 : Dyadic) * half ^ 9),
        ((217 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((139 : Dyadic) * half ^ 10),
        ((29 : Dyadic) * half ^ 8)⟩,
       ⟨((41 : Dyadic) * half ^ 7),
        ((-455 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word18Step12 :
    word18Chunk12.foldl (fun acc a => a.applyPacked acc)
      word18State12 = word18State13 := by decide +kernel

private def word18Chunk13 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word18State14 : PackedMat2 :=
    ⟨⟨⟨((219 : Dyadic) * half ^ 11),
        ((835 : Dyadic) * half ^ 12)⟩,
       ⟨((-333 : Dyadic) * half ^ 9),
        ((-1 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((289 : Dyadic) * half ^ 10),
        ((1021 : Dyadic) * half ^ 12)⟩,
       ⟨((-617 : Dyadic) * half ^ 11),
        ((1255 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-289 : Dyadic) * half ^ 10),
        ((-1021 : Dyadic) * half ^ 12)⟩,
       ⟨((-617 : Dyadic) * half ^ 11),
        ((1255 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((219 : Dyadic) * half ^ 11),
        ((835 : Dyadic) * half ^ 12)⟩,
       ⟨((333 : Dyadic) * half ^ 9),
        ((1 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word18Step13 :
    word18Chunk13.foldl (fun acc a => a.applyPacked acc)
      word18State13 = word18State14 := by decide +kernel

private def word18Chunk14 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word18State15 : PackedMat2 :=
    ⟨⟨⟨((103 : Dyadic) * half ^ 8),
        ((-239 : Dyadic) * half ^ 12)⟩,
       ⟨((1553 : Dyadic) * half ^ 11),
        ((-79 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((85 : Dyadic) * half ^ 10),
        ((235 : Dyadic) * half ^ 12)⟩,
       ⟨((479 : Dyadic) * half ^ 10),
        ((105 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-185 : Dyadic) * half ^ 12),
        ((-197 : Dyadic) * half ^ 10)⟩,
       ⟨((-655 : Dyadic) * half ^ 12),
        ((-141 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((81 : Dyadic) * half ^ 12),
        ((729 : Dyadic) * half ^ 12)⟩,
       ⟨((-397 : Dyadic) * half ^ 12),
        ((2377 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word18Step14 :
    word18Chunk14.foldl (fun acc a => a.applyPacked acc)
      word18State14 = word18State15 := by decide +kernel

private def word18Chunk15 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word18State16 : PackedMat2 :=
    ⟨⟨⟨((-6751 : Dyadic) * half ^ 13),
        ((-47 : Dyadic) * half ^ 9)⟩,
       ⟨((-2195 : Dyadic) * half ^ 13),
        ((2061 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((665 : Dyadic) * half ^ 13),
        ((-1601 : Dyadic) * half ^ 13)⟩,
       ⟨((727 : Dyadic) * half ^ 13),
        ((11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((727 : Dyadic) * half ^ 13),
        ((11 : Dyadic) * half ^ 7)⟩,
       ⟨((665 : Dyadic) * half ^ 13),
        ((-1601 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2195 : Dyadic) * half ^ 13),
        ((-2061 : Dyadic) * half ^ 13)⟩,
       ⟨((6751 : Dyadic) * half ^ 13),
        ((47 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word18Step15 :
    word18Chunk15.foldl (fun acc a => a.applyPacked acc)
      word18State15 = word18State16 := by decide +kernel

private def word18Chunk16 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word18State17 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 12),
        ((-2379 : Dyadic) * half ^ 12)⟩,
       ⟨((-1647 : Dyadic) * half ^ 13),
        ((-673 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1531 : Dyadic) * half ^ 12),
        ((1011 : Dyadic) * half ^ 13)⟩,
       ⟨((-2339 : Dyadic) * half ^ 13),
        ((-813 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-99 : Dyadic) * half ^ 12),
        ((5401 : Dyadic) * half ^ 14)⟩,
       ⟨((-57 : Dyadic) * half ^ 8),
        ((723 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5431 : Dyadic) * half ^ 13),
        ((-1665 : Dyadic) * half ^ 14)⟩,
       ⟨((-4085 : Dyadic) * half ^ 13),
        ((1629 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word18Step16 :
    word18Chunk16.foldl (fun acc a => a.applyPacked acc)
      word18State16 = word18State17 := by decide +kernel

private def word18Chunk17 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word18State18 : PackedMat2 :=
    ⟨⟨⟨((47 : Dyadic) * half ^ 13),
        ((1445 : Dyadic) * half ^ 13)⟩,
       ⟨((-5707 : Dyadic) * half ^ 14),
        ((3827 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4403 : Dyadic) * half ^ 13),
        ((1655 : Dyadic) * half ^ 14)⟩,
       ⟨((-8303 : Dyadic) * half ^ 14),
        ((-4353 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-8303 : Dyadic) * half ^ 14),
        ((-4353 : Dyadic) * half ^ 14)⟩,
       ⟨((-4403 : Dyadic) * half ^ 13),
        ((1655 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((5707 : Dyadic) * half ^ 14),
        ((-3827 : Dyadic) * half ^ 14)⟩,
       ⟨((-47 : Dyadic) * half ^ 13),
        ((-1445 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word18Step17 :
    word18Chunk17.foldl (fun acc a => a.applyPacked acc)
      word18State17 = word18State18 := by decide +kernel

private def word18Chunk18 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word18State19 : PackedMat2 :=
    ⟨⟨⟨((14185 : Dyadic) * half ^ 15),
        ((9643 : Dyadic) * half ^ 16)⟩,
       ⟨((435 : Dyadic) * half ^ 13),
        ((-5131 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((9165 : Dyadic) * half ^ 14),
        ((-14519 : Dyadic) * half ^ 16)⟩,
       ⟨((-18449 : Dyadic) * half ^ 15),
        ((-7495 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((11007 : Dyadic) * half ^ 15),
        ((119 : Dyadic) * half ^ 16)⟩,
       ⟨((439 : Dyadic) * half ^ 12),
        ((-36779 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((141 : Dyadic) * half ^ 11),
        ((15925 : Dyadic) * half ^ 16)⟩,
       ⟨((7387 : Dyadic) * half ^ 15),
        ((12445 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word18Step18 :
    word18Chunk18.foldl (fun acc a => a.applyPacked acc)
      word18State18 = word18State19 := by decide +kernel

private def word18Chunk19 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State20 : PackedMat2 :=
    ⟨⟨⟨((2469 : Dyadic) * half ^ 16),
        ((2013 : Dyadic) * half ^ 15)⟩,
       ⟨((18213 : Dyadic) * half ^ 16),
        ((-95 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1137 : Dyadic) * half ^ 16),
        ((37359 : Dyadic) * half ^ 16)⟩,
       ⟨((33159 : Dyadic) * half ^ 16),
        ((2651 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1137 : Dyadic) * half ^ 16),
        ((37359 : Dyadic) * half ^ 16)⟩,
       ⟨((-33159 : Dyadic) * half ^ 16),
        ((-2651 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-2469 : Dyadic) * half ^ 16),
        ((-2013 : Dyadic) * half ^ 15)⟩,
       ⟨((18213 : Dyadic) * half ^ 16),
        ((-95 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word18Step19 :
    word18Chunk19.foldl (fun acc a => a.applyPacked acc)
      word18State19 = word18State20 := by decide +kernel

private def word18Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word18State21 : PackedMat2 :=
    ⟨⟨⟨((-50171 : Dyadic) * half ^ 17),
        ((-5251 : Dyadic) * half ^ 16)⟩,
       ⟨((-38319 : Dyadic) * half ^ 17),
        ((39387 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((42545 : Dyadic) * half ^ 17),
        ((6553 : Dyadic) * half ^ 17)⟩,
       ⟨((11231 : Dyadic) * half ^ 17),
        ((31323 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((56093 : Dyadic) * half ^ 17),
        ((-15657 : Dyadic) * half ^ 17)⟩,
       ⟨((69199 : Dyadic) * half ^ 17),
        ((3361 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-49889 : Dyadic) * half ^ 17),
        ((-2963 : Dyadic) * half ^ 16)⟩,
       ⟨((-28885 : Dyadic) * half ^ 17),
        ((44245 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word18Step20 :
    word18Chunk20.foldl (fun acc a => a.applyPacked acc)
      word18State20 = word18State21 := by decide +kernel

private def word18Chunk21 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State22 : PackedMat2 :=
    ⟨⟨⟨((47347 : Dyadic) * half ^ 17),
        ((-12617 : Dyadic) * half ^ 16)⟩,
       ⟨((10779 : Dyadic) * half ^ 15),
        ((-33623 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-79879 : Dyadic) * half ^ 17),
        ((-14867 : Dyadic) * half ^ 16)⟩,
       ⟨((17907 : Dyadic) * half ^ 16),
        ((235 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-17907 : Dyadic) * half ^ 16),
        ((-235 : Dyadic) * half ^ 12)⟩,
       ⟨((79879 : Dyadic) * half ^ 17),
        ((14867 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((10779 : Dyadic) * half ^ 15),
        ((-33623 : Dyadic) * half ^ 17)⟩,
       ⟨((47347 : Dyadic) * half ^ 17),
        ((-12617 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word18Step21 :
    word18Chunk21.foldl (fun acc a => a.applyPacked acc)
      word18State21 = word18State22 := by decide +kernel

private def word18Chunk22 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word18State23 : PackedMat2 :=
    ⟨⟨⟨((-4703 : Dyadic) * half ^ 16),
        ((122281 : Dyadic) * half ^ 19)⟩,
       ⟨((2195 : Dyadic) * half ^ 18),
        ((-181413 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-181023 : Dyadic) * half ^ 18),
        ((-51327 : Dyadic) * half ^ 19)⟩,
       ⟨((-27079 : Dyadic) * half ^ 17),
        ((121733 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-181023 : Dyadic) * half ^ 18),
        ((-51327 : Dyadic) * half ^ 19)⟩,
       ⟨((27079 : Dyadic) * half ^ 17),
        ((-121733 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((4703 : Dyadic) * half ^ 16),
        ((-122281 : Dyadic) * half ^ 19)⟩,
       ⟨((2195 : Dyadic) * half ^ 18),
        ((-181413 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word18Step22 :
    word18Chunk22.foldl (fun acc a => a.applyPacked acc)
      word18State22 = word18State23 := by decide +kernel

private def word18Chunk23 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word18State24 : PackedMat2 :=
    ⟨⟨⟨((-155349 : Dyadic) * half ^ 19),
        ((-102043 : Dyadic) * half ^ 20)⟩,
       ⟨((18353 : Dyadic) * half ^ 18),
        ((-559945 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-30315 : Dyadic) * half ^ 18),
        ((-5549 : Dyadic) * half ^ 20)⟩,
       ⟨((-10673 : Dyadic) * half ^ 19),
        ((-408941 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((207245 : Dyadic) * half ^ 19),
        ((71303 : Dyadic) * half ^ 20)⟩,
       ⟨((-6303 : Dyadic) * half ^ 14),
        ((49957 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-165497 : Dyadic) * half ^ 18),
        ((-118643 : Dyadic) * half ^ 20)⟩,
       ⟨((228951 : Dyadic) * half ^ 19),
        ((-192055 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word18Step23 :
    word18Chunk23.foldl (fun acc a => a.applyPacked acc)
      word18State23 = word18State24 := by decide +kernel

private def word18Chunk24 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word18State25 : PackedMat2 :=
    ⟨⟨⟨((-365147 : Dyadic) * half ^ 19),
        ((66989 : Dyadic) * half ^ 19)⟩,
       ⟨((-72949 : Dyadic) * half ^ 19),
        ((-259945 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1153 : Dyadic) * half ^ 14),
        ((112683 : Dyadic) * half ^ 19)⟩,
       ⟨((-250975 : Dyadic) * half ^ 19),
        ((-86239 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1153 : Dyadic) * half ^ 14),
        ((112683 : Dyadic) * half ^ 19)⟩,
       ⟨((250975 : Dyadic) * half ^ 19),
        ((86239 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((365147 : Dyadic) * half ^ 19),
        ((-66989 : Dyadic) * half ^ 19)⟩,
       ⟨((-72949 : Dyadic) * half ^ 19),
        ((-259945 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word18Step24 :
    word18Chunk24.foldl (fun acc a => a.applyPacked acc)
      word18State24 = word18State25 := by decide +kernel

private def word18Chunk25 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State26 : PackedMat2 :=
    ⟨⟨⟨((1343907 : Dyadic) * half ^ 21),
        ((59135 : Dyadic) * half ^ 21)⟩,
       ⟨((-208413 : Dyadic) * half ^ 21),
        ((21033 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((1470057 : Dyadic) * half ^ 21),
        ((7383 : Dyadic) * half ^ 20)⟩,
       ⟨((568971 : Dyadic) * half ^ 21),
        ((-162419 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-177185 : Dyadic) * half ^ 21),
        ((-450543 : Dyadic) * half ^ 21)⟩,
       ⟨((-147653 : Dyadic) * half ^ 21),
        ((509757 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((17069 : Dyadic) * half ^ 21),
        ((24255 : Dyadic) * half ^ 16)⟩,
       ⟨((-101201 : Dyadic) * half ^ 21),
        ((-567747 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word18Step25 :
    word18Chunk25.foldl (fun acc a => a.applyPacked acc)
      word18State25 = word18State26 := by decide +kernel

private def word18Chunk26 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State27 : PackedMat2 :=
    ⟨⟨⟨((-647805 : Dyadic) * half ^ 21),
        ((7013 : Dyadic) * half ^ 17)⟩,
       ⟨((376467 : Dyadic) * half ^ 20),
        ((802165 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-922387 : Dyadic) * half ^ 21),
        ((343589 : Dyadic) * half ^ 20)⟩,
       ⟨((81529 : Dyadic) * half ^ 19),
        ((78619 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-81529 : Dyadic) * half ^ 19),
        ((-78619 : Dyadic) * half ^ 19)⟩,
       ⟨((922387 : Dyadic) * half ^ 21),
        ((-343589 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((376467 : Dyadic) * half ^ 20),
        ((802165 : Dyadic) * half ^ 21)⟩,
       ⟨((-647805 : Dyadic) * half ^ 21),
        ((7013 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word18Step26 :
    word18Chunk26.foldl (fun acc a => a.applyPacked acc)
      word18State26 = word18State27 := by decide +kernel

private def word18Chunk27 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word18State28 : PackedMat2 :=
    ⟨⟨⟨((-19477 : Dyadic) * half ^ 19),
        ((-4148443 : Dyadic) * half ^ 23)⟩,
       ⟨((-45129 : Dyadic) * half ^ 22),
        ((2326555 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1738197 : Dyadic) * half ^ 22),
        ((-1072987 : Dyadic) * half ^ 23)⟩,
       ⟨((310469 : Dyadic) * half ^ 21),
        ((2131717 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1738197 : Dyadic) * half ^ 22),
        ((-1072987 : Dyadic) * half ^ 23)⟩,
       ⟨((-310469 : Dyadic) * half ^ 21),
        ((-2131717 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((19477 : Dyadic) * half ^ 19),
        ((4148443 : Dyadic) * half ^ 23)⟩,
       ⟨((-45129 : Dyadic) * half ^ 22),
        ((2326555 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word18Step27 :
    word18Chunk27.foldl (fun acc a => a.applyPacked acc)
      word18State27 = word18State28 := by decide +kernel

private def word18Chunk28 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word18State29 : PackedMat2 :=
    ⟨⟨⟨((-5841511 : Dyadic) * half ^ 23),
        ((-97825 : Dyadic) * half ^ 20)⟩,
       ⟨((2791677 : Dyadic) * half ^ 23),
        ((-263373 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1849741 : Dyadic) * half ^ 23),
        ((-1401883 : Dyadic) * half ^ 23)⟩,
       ⟨((3915043 : Dyadic) * half ^ 23),
        ((-1078833 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((161525 : Dyadic) * half ^ 22),
        ((360299 : Dyadic) * half ^ 20)⟩,
       ⟨((-620179 : Dyadic) * half ^ 21),
        ((1032651 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((67723 : Dyadic) * half ^ 21),
        ((-2158297 : Dyadic) * half ^ 22)⟩,
       ⟨((459023 : Dyadic) * half ^ 21),
        ((1524917 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word18Step28 :
    word18Chunk28.foldl (fun acc a => a.applyPacked acc)
      word18State28 = word18State29 := by decide +kernel

private def word18Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word18State30 : PackedMat2 :=
    ⟨⟨⟨((-11216097 : Dyadic) * half ^ 24),
        ((1154887 : Dyadic) * half ^ 24)⟩,
       ⟨((1964669 : Dyadic) * half ^ 24),
        ((-5655639 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-4124725 : Dyadic) * half ^ 24),
        ((-2917407 : Dyadic) * half ^ 23)⟩,
       ⟨((11817 : Dyadic) * half ^ 24),
        ((-46965 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-4124725 : Dyadic) * half ^ 24),
        ((-2917407 : Dyadic) * half ^ 23)⟩,
       ⟨((-11817 : Dyadic) * half ^ 24),
        ((46965 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((11216097 : Dyadic) * half ^ 24),
        ((-1154887 : Dyadic) * half ^ 24)⟩,
       ⟨((1964669 : Dyadic) * half ^ 24),
        ((-5655639 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word18Step29 :
    word18Chunk29.foldl (fun acc a => a.applyPacked acc)
      word18State29 = word18State30 := by decide +kernel

private def word18Chunk30 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word18State31 : PackedMat2 :=
    ⟨⟨⟨((5992059 : Dyadic) * half ^ 25),
        ((-3492187 : Dyadic) * half ^ 25)⟩,
       ⟨((-28550049 : Dyadic) * half ^ 25),
        ((531551 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-4870919 : Dyadic) * half ^ 25),
        ((-657953 : Dyadic) * half ^ 21)⟩,
       ⟨((307 : Dyadic) * half ^ 25),
        ((-1197283 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((9329965 : Dyadic) * half ^ 25),
        ((2435613 : Dyadic) * half ^ 25)⟩,
       ⟨((-11724531 : Dyadic) * half ^ 25),
        ((-1217653 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-4555289 : Dyadic) * half ^ 25),
        ((8635527 : Dyadic) * half ^ 24)⟩,
       ⟨((2429085 : Dyadic) * half ^ 25),
        ((11278995 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word18Step30 :
    word18Chunk30.foldl (fun acc a => a.applyPacked acc)
      word18State30 = word18State31 := by decide +kernel

private def word18Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word18State32 : PackedMat2 :=
    ⟨⟨⟨((-3934525 : Dyadic) * half ^ 26),
        ((18715989 : Dyadic) * half ^ 25)⟩,
       ⟨((-26824915 : Dyadic) * half ^ 26),
        ((-11867433 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((3210879 : Dyadic) * half ^ 26),
        ((-7579647 : Dyadic) * half ^ 26)⟩,
       ⟨((-9600273 : Dyadic) * half ^ 26),
        ((1910473 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-22863431 : Dyadic) * half ^ 26),
        ((800697 : Dyadic) * half ^ 23)⟩,
       ⟨((-7704137 : Dyadic) * half ^ 26),
        ((3194697 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-49299411 : Dyadic) * half ^ 26),
        ((-11445195 : Dyadic) * half ^ 26)⟩,
       ⟨((25564545 : Dyadic) * half ^ 26),
        ((-1922465 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word18Step31 :
    word18Chunk31.foldl (fun acc a => a.applyPacked acc)
      word18State31 = word18State32 := by decide +kernel

private def word18Chunk32 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word18State33 : PackedMat2 :=
    ⟨⟨⟨((46044299 : Dyadic) * half ^ 26),
        ((5804173 : Dyadic) * half ^ 25)⟩,
       ⟨((-1528657 : Dyadic) * half ^ 23),
        ((378427 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((10632947 : Dyadic) * half ^ 26),
        ((-6421 : Dyadic) * half ^ 22)⟩,
       ⟨((9428243 : Dyadic) * half ^ 25),
        ((-27305949 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((9428243 : Dyadic) * half ^ 25),
        ((-27305949 : Dyadic) * half ^ 26)⟩,
       ⟨((10632947 : Dyadic) * half ^ 26),
        ((-6421 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1528657 : Dyadic) * half ^ 23),
        ((-378427 : Dyadic) * half ^ 24)⟩,
       ⟨((-46044299 : Dyadic) * half ^ 26),
        ((-5804173 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word18Step32 :
    word18Chunk32.foldl (fun acc a => a.applyPacked acc)
      word18State32 = word18State33 := by decide +kernel

private def word18Chunk33 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word18State34 : PackedMat2 :=
    ⟨⟨⟨((52539123 : Dyadic) * half ^ 27),
        ((108616217 : Dyadic) * half ^ 28)⟩,
       ⟨((6543729 : Dyadic) * half ^ 26),
        ((-31823975 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-5982685 : Dyadic) * half ^ 24),
        ((86923275 : Dyadic) * half ^ 28)⟩,
       ⟨((48330519 : Dyadic) * half ^ 27),
        ((-23377139 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((5982685 : Dyadic) * half ^ 24),
        ((-86923275 : Dyadic) * half ^ 28)⟩,
       ⟨((48330519 : Dyadic) * half ^ 27),
        ((-23377139 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((52539123 : Dyadic) * half ^ 27),
        ((108616217 : Dyadic) * half ^ 28)⟩,
       ⟨((-6543729 : Dyadic) * half ^ 26),
        ((31823975 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word18Step33 :
    word18Chunk33.foldl (fun acc a => a.applyPacked acc)
      word18State33 = word18State34 := by decide +kernel

private def word18Chunk34 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word18State35 : PackedMat2 :=
    ⟨⟨⟨((-12639173 : Dyadic) * half ^ 26),
        ((29425711 : Dyadic) * half ^ 28)⟩,
       ⟨((54810427 : Dyadic) * half ^ 27),
        ((51633953 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((7806329 : Dyadic) * half ^ 24),
        ((-60143235 : Dyadic) * half ^ 28)⟩,
       ⟨((-25703763 : Dyadic) * half ^ 26),
        ((5642859 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-82714671 : Dyadic) * half ^ 28),
        ((56929079 : Dyadic) * half ^ 27)⟩,
       ⟨((37571799 : Dyadic) * half ^ 28),
        ((-5521553 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((73842195 : Dyadic) * half ^ 28),
        ((80088773 : Dyadic) * half ^ 28)⟩,
       ⟨((132693617 : Dyadic) * half ^ 28),
        ((29532081 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word18Step34 :
    word18Chunk34.foldl (fun acc a => a.applyPacked acc)
      word18State34 = word18State35 := by decide +kernel

private def word18Chunk35 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word18State36 : PackedMat2 :=
    ⟨⟨⟨((31945239 : Dyadic) * half ^ 29),
        ((-66920689 : Dyadic) * half ^ 27)⟩,
       ⟨((118407321 : Dyadic) * half ^ 29),
        ((150089671 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-91313613 : Dyadic) * half ^ 29),
        ((22241055 : Dyadic) * half ^ 29)⟩,
       ⟨((37350519 : Dyadic) * half ^ 29),
        ((-1503831 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((37350519 : Dyadic) * half ^ 29),
        ((-1503831 : Dyadic) * half ^ 22)⟩,
       ⟨((-91313613 : Dyadic) * half ^ 29),
        ((22241055 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-118407321 : Dyadic) * half ^ 29),
        ((-150089671 : Dyadic) * half ^ 29)⟩,
       ⟨((-31945239 : Dyadic) * half ^ 29),
        ((66920689 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word18Step35 :
    word18Chunk35.foldl (fun acc a => a.applyPacked acc)
      word18State35 = word18State36 := by decide +kernel

private def word18Chunk36 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word18State37 : PackedMat2 :=
    ⟨⟨⟨((-712157733 : Dyadic) * half ^ 30),
        ((-227680641 : Dyadic) * half ^ 30)⟩,
       ⟨((-384135811 : Dyadic) * half ^ 30),
        ((180872009 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((154974293 : Dyadic) * half ^ 30),
        ((-42134775 : Dyadic) * half ^ 28)⟩,
       ⟨((227237605 : Dyadic) * half ^ 30),
        ((12909529 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-227237605 : Dyadic) * half ^ 30),
        ((-12909529 : Dyadic) * half ^ 30)⟩,
       ⟨((-154974293 : Dyadic) * half ^ 30),
        ((42134775 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-384135811 : Dyadic) * half ^ 30),
        ((180872009 : Dyadic) * half ^ 29)⟩,
       ⟨((-712157733 : Dyadic) * half ^ 30),
        ((-227680641 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word18Step36 :
    word18Chunk36.foldl (fun acc a => a.applyPacked acc)
      word18State36 = word18State37 := by decide +kernel

private def word18Chunk37 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word18State38 : PackedMat2 :=
    ⟨⟨⟨((-1295354897 : Dyadic) * half ^ 31),
        ((187163921 : Dyadic) * half ^ 31)⟩,
       ⟨((296630647 : Dyadic) * half ^ 31),
        ((-119617659 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((581218325 : Dyadic) * half ^ 31),
        ((-38114711 : Dyadic) * half ^ 29)⟩,
       ⟨((-390035669 : Dyadic) * half ^ 31),
        ((-1030726507 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-878267663 : Dyadic) * half ^ 31),
        ((-485626997 : Dyadic) * half ^ 31)⟩,
       ⟨((-1183185351 : Dyadic) * half ^ 31),
        ((2987229 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((426399239 : Dyadic) * half ^ 31),
        ((-198998193 : Dyadic) * half ^ 29)⟩,
       ⟨((52071397 : Dyadic) * half ^ 31),
        ((499362125 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word18Step37 :
    word18Chunk37.foldl (fun acc a => a.applyPacked acc)
      word18State37 = word18State38 := by decide +kernel

private def word18Chunk38 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word18State39 : PackedMat2 :=
    ⟨⟨⟨((-382894639 : Dyadic) * half ^ 31),
        ((412664111 : Dyadic) * half ^ 32)⟩,
       ⟨((-120969069 : Dyadic) * half ^ 31),
        ((648330047 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-159582649 : Dyadic) * half ^ 30),
        ((1769851763 : Dyadic) * half ^ 32)⟩,
       ⟨((-184789101 : Dyadic) * half ^ 30),
        ((-2168174473 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((184789101 : Dyadic) * half ^ 30),
        ((2168174473 : Dyadic) * half ^ 32)⟩,
       ⟨((159582649 : Dyadic) * half ^ 30),
        ((-1769851763 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-120969069 : Dyadic) * half ^ 31),
        ((648330047 : Dyadic) * half ^ 32)⟩,
       ⟨((-382894639 : Dyadic) * half ^ 31),
        ((412664111 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word18Step38 :
    word18Chunk38.foldl (fun acc a => a.applyPacked acc)
      word18State38 = word18State39 := by decide +kernel

private def word18Chunk39 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State40 : PackedMat2 :=
    ⟨⟨⟨((377804471 : Dyadic) * half ^ 31),
        ((845254745 : Dyadic) * half ^ 33)⟩,
       ⟨((587736807 : Dyadic) * half ^ 32),
        ((-2509381407 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2536787549 : Dyadic) * half ^ 32),
        ((1097065661 : Dyadic) * half ^ 33)⟩,
       ⟨((-265821545 : Dyadic) * half ^ 31),
        ((3661946847 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1189753127 : Dyadic) * half ^ 31),
        ((2005144459 : Dyadic) * half ^ 33)⟩,
       ⟨((-1282440593 : Dyadic) * half ^ 32),
        ((3068430639 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((832063331 : Dyadic) * half ^ 32),
        ((-1343345749 : Dyadic) * half ^ 33)⟩,
       ⟨((-419329519 : Dyadic) * half ^ 30),
        ((-167872135 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word18Step39 :
    word18Chunk39.foldl (fun acc a => a.applyPacked acc)
      word18State39 = word18State40 := by decide +kernel

private def word18Chunk40 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word18State41 : PackedMat2 :=
    ⟨⟨⟨((333325317 : Dyadic) * half ^ 33),
        ((-582948413 : Dyadic) * half ^ 31)⟩,
       ⟨((4112918047 : Dyadic) * half ^ 33),
        ((1662791017 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((2590208313 : Dyadic) * half ^ 33),
        ((52524041 : Dyadic) * half ^ 33)⟩,
       ⟨((-1569757159 : Dyadic) * half ^ 33),
        ((987051643 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1569757159 : Dyadic) * half ^ 33),
        ((987051643 : Dyadic) * half ^ 31)⟩,
       ⟨((2590208313 : Dyadic) * half ^ 33),
        ((52524041 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-4112918047 : Dyadic) * half ^ 33),
        ((-1662791017 : Dyadic) * half ^ 33)⟩,
       ⟨((-333325317 : Dyadic) * half ^ 33),
        ((582948413 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word18Step40 :
    word18Chunk40.foldl (fun acc a => a.applyPacked acc)
      word18State40 = word18State41 := by decide +kernel

private def word18Chunk41 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word18State42 : PackedMat2 :=
    ⟨⟨⟨((8914445345 : Dyadic) * half ^ 34),
        ((-1627728175 : Dyadic) * half ^ 33)⟩,
       ⟨((5691240103 : Dyadic) * half ^ 34),
        ((2021443461 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-11318478363 : Dyadic) * half ^ 34),
        ((-826510185 : Dyadic) * half ^ 34)⟩,
       ⟨((2863133957 : Dyadic) * half ^ 34),
        ((356306677 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-3676963601 : Dyadic) * half ^ 34),
        ((-443175385 : Dyadic) * half ^ 30)⟩,
       ⟨((-2023943231 : Dyadic) * half ^ 34),
        ((4227672203 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5276899811 : Dyadic) * half ^ 34),
        ((-1611602621 : Dyadic) * half ^ 34)⟩,
       ⟨((-1234012889 : Dyadic) * half ^ 34),
        ((1825710681 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word18Step41 :
    word18Chunk41.foldl (fun acc a => a.applyPacked acc)
      word18State41 = word18State42 := by decide +kernel

private def word18Chunk42 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State43 : PackedMat2 :=
    ⟨⟨⟨((-5889887215 : Dyadic) * half ^ 33),
        ((-2122595325 : Dyadic) * half ^ 34)⟩,
       ⟨((-17375439 : Dyadic) * half ^ 34),
        ((1563403779 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1256910077 : Dyadic) * half ^ 32),
        ((-2681588003 : Dyadic) * half ^ 33)⟩,
       ⟨((-6695840989 : Dyadic) * half ^ 34),
        ((-75224135 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-6695840989 : Dyadic) * half ^ 34),
        ((-75224135 : Dyadic) * half ^ 32)⟩,
       ⟨((1256910077 : Dyadic) * half ^ 32),
        ((-2681588003 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((17375439 : Dyadic) * half ^ 34),
        ((-1563403779 : Dyadic) * half ^ 33)⟩,
       ⟨((5889887215 : Dyadic) * half ^ 33),
        ((2122595325 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word18Step42 :
    word18Chunk42.foldl (fun acc a => a.applyPacked acc)
      word18State42 = word18State43 := by decide +kernel

private def word18Chunk43 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word18State44 : PackedMat2 :=
    ⟨⟨⟨((-12147554425 : Dyadic) * half ^ 35),
        ((2493313989 : Dyadic) * half ^ 33)⟩,
       ⟨((-6900339845 : Dyadic) * half ^ 35),
        ((-4458514563 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-83849343 : Dyadic) * half ^ 35),
        ((-12550245925 : Dyadic) * half ^ 35)⟩,
       ⟨((-16990147899 : Dyadic) * half ^ 35),
        ((-3447162945 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((2275770745 : Dyadic) * half ^ 33),
        ((-4226574639 : Dyadic) * half ^ 34)⟩,
       ⟨((-7998704435 : Dyadic) * half ^ 34),
        ((-8536998621 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((9445142541 : Dyadic) * half ^ 34),
        ((-1311803645 : Dyadic) * half ^ 34)⟩,
       ⟨((-528113415 : Dyadic) * half ^ 34),
        ((9523947135 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word18Step43 :
    word18Chunk43.foldl (fun acc a => a.applyPacked acc)
      word18State43 = word18State44 := by decide +kernel

private def word18Chunk44 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word18State45 : PackedMat2 :=
    ⟨⟨⟨((29583409517 : Dyadic) * half ^ 36),
        ((1782881583 : Dyadic) * half ^ 35)⟩,
       ⟨((-15300857847 : Dyadic) * half ^ 36),
        ((-13999725417 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((14249758227 : Dyadic) * half ^ 36),
        ((-7672901573 : Dyadic) * half ^ 36)⟩,
       ⟨((-15766200197 : Dyadic) * half ^ 36),
        ((26928876417 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((14249758227 : Dyadic) * half ^ 36),
        ((-7672901573 : Dyadic) * half ^ 36)⟩,
       ⟨((15766200197 : Dyadic) * half ^ 36),
        ((-26928876417 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-29583409517 : Dyadic) * half ^ 36),
        ((-1782881583 : Dyadic) * half ^ 35)⟩,
       ⟨((-15300857847 : Dyadic) * half ^ 36),
        ((-13999725417 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word18Step44 :
    word18Chunk44.foldl (fun acc a => a.applyPacked acc)
      word18State44 = word18State45 := by decide +kernel

private def word18Chunk45 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word18State46 : PackedMat2 :=
    ⟨⟨⟨((3176409335 : Dyadic) * half ^ 37),
        ((7292635167 : Dyadic) * half ^ 34)⟩,
       ⟨((8186285839 : Dyadic) * half ^ 37),
        ((-26743073893 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-24013290617 : Dyadic) * half ^ 37),
        ((-5537842355 : Dyadic) * half ^ 37)⟩,
       ⟨((99672725061 : Dyadic) * half ^ 37),
        ((-124621011 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((4540874267 : Dyadic) * half ^ 37),
        ((61843007839 : Dyadic) * half ^ 37)⟩,
       ⟨((-6534810443 : Dyadic) * half ^ 37),
        ((18914858611 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((85084155229 : Dyadic) * half ^ 37),
        ((-626234563 : Dyadic) * half ^ 35)⟩,
       ⟨((-31598007443 : Dyadic) * half ^ 37),
        ((-5681347587 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word18Step45 :
    word18Chunk45.foldl (fun acc a => a.applyPacked acc)
      word18State45 = word18State46 := by decide +kernel

private def word18Chunk46 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State47 : PackedMat2 :=
    ⟨⟨⟨((39131167161 : Dyadic) * half ^ 37),
        ((433438471 : Dyadic) * half ^ 32)⟩,
       ⟨((1253332531 : Dyadic) * half ^ 34),
        ((64297610019 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((2441923259 : Dyadic) * half ^ 37),
        ((-1806660489 : Dyadic) * half ^ 33)⟩,
       ⟨((-40454708391 : Dyadic) * half ^ 36),
        ((3450936921 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((40454708391 : Dyadic) * half ^ 36),
        ((-3450936921 : Dyadic) * half ^ 35)⟩,
       ⟨((-2441923259 : Dyadic) * half ^ 37),
        ((1806660489 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((1253332531 : Dyadic) * half ^ 34),
        ((64297610019 : Dyadic) * half ^ 37)⟩,
       ⟨((39131167161 : Dyadic) * half ^ 37),
        ((433438471 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word18Step46 :
    word18Chunk46.foldl (fun acc a => a.applyPacked acc)
      word18State46 = word18State47 := by decide +kernel

private def word18Chunk47 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word18State48 : PackedMat2 :=
    ⟨⟨⟨((-62274352925 : Dyadic) * half ^ 38),
        ((67722294515 : Dyadic) * half ^ 38)⟩,
       ⟨((36406433323 : Dyadic) * half ^ 36),
        ((75688735199 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-46002453391 : Dyadic) * half ^ 38),
        ((104806087939 : Dyadic) * half ^ 38)⟩,
       ⟨((-5904514151 : Dyadic) * half ^ 35),
        ((10497944187 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-5904514151 : Dyadic) * half ^ 35),
        ((10497944187 : Dyadic) * half ^ 36)⟩,
       ⟨((-46002453391 : Dyadic) * half ^ 38),
        ((104806087939 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-36406433323 : Dyadic) * half ^ 36),
        ((-75688735199 : Dyadic) * half ^ 38)⟩,
       ⟨((62274352925 : Dyadic) * half ^ 38),
        ((-67722294515 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word18Step47 :
    word18Chunk47.foldl (fun acc a => a.applyPacked acc)
      word18State47 = word18State48 := by decide +kernel

private def word18Chunk48 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word18State49 : PackedMat2 :=
    ⟨⟨⟨((-138553934259 : Dyadic) * half ^ 39),
        ((-410738592149 : Dyadic) * half ^ 40)⟩,
       ⟨((-55245754947 : Dyadic) * half ^ 38),
        ((277030674877 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((5213572249 : Dyadic) * half ^ 38),
        ((-443739539955 : Dyadic) * half ^ 40)⟩,
       ⟨((210305877429 : Dyadic) * half ^ 39),
        ((-103054533247 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((273397036601 : Dyadic) * half ^ 39),
        ((-220733021927 : Dyadic) * half ^ 40)⟩,
       ⟨((85171251677 : Dyadic) * half ^ 38),
        ((199878732931 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-16713489659 : Dyadic) * half ^ 37),
        ((-249045444153 : Dyadic) * half ^ 40)⟩,
       ⟨((-343884633513 : Dyadic) * half ^ 39),
        ((-28062424365 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word18Step48 :
    word18Chunk48.foldl (fun acc a => a.applyPacked acc)
      word18State48 = word18State49 := by decide +kernel

private def word18Chunk49 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word18State50 : PackedMat2 :=
    ⟨⟨⟨((-231615334479 : Dyadic) * half ^ 40),
        ((-402655710441 : Dyadic) * half ^ 40)⟩,
       ⟨((-391284984235 : Dyadic) * half ^ 40),
        ((16411220229 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((766262748871 : Dyadic) * half ^ 40),
        ((-28208943171 : Dyadic) * half ^ 38)⟩,
       ⟨((-137382094455 : Dyadic) * half ^ 40),
        ((-137474017727 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((137382094455 : Dyadic) * half ^ 40),
        ((137474017727 : Dyadic) * half ^ 40)⟩,
       ⟨((-766262748871 : Dyadic) * half ^ 40),
        ((28208943171 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-391284984235 : Dyadic) * half ^ 40),
        ((16411220229 : Dyadic) * half ^ 38)⟩,
       ⟨((-231615334479 : Dyadic) * half ^ 40),
        ((-402655710441 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word18Step49 :
    word18Chunk49.foldl (fun acc a => a.applyPacked acc)
      word18State49 = word18State50 := by decide +kernel

private def word18Chunk50 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word18State51 : PackedMat2 :=
    ⟨⟨⟨((-644701490409 : Dyadic) * half ^ 41),
        ((67122755639 : Dyadic) * half ^ 41)⟩,
       ⟨((-1419739257969 : Dyadic) * half ^ 41),
        ((-40574069095 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((1446764739345 : Dyadic) * half ^ 41),
        ((-42261675229 : Dyadic) * half ^ 40)⟩,
       ⟨((209702165863 : Dyadic) * half ^ 41),
        ((-309290326293 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-224766975835 : Dyadic) * half ^ 41),
        ((-618531286741 : Dyadic) * half ^ 41)⟩,
       ⟨((-393813676751 : Dyadic) * half ^ 41),
        ((207058363151 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((229419032019 : Dyadic) * half ^ 41),
        ((96879720945 : Dyadic) * half ^ 39)⟩,
       ⟨((95173520741 : Dyadic) * half ^ 41),
        ((1032220374189 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word18Step50 :
    word18Chunk50.foldl (fun acc a => a.applyPacked acc)
      word18State50 = word18State51 := by decide +kernel

private def word18Chunk51 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word18State52 : PackedMat2 :=
    ⟨⟨⟨((881843467555 : Dyadic) * half ^ 41),
        ((-395847770161 : Dyadic) * half ^ 41)⟩,
       ⟨((29841918511 : Dyadic) * half ^ 38),
        ((-359284963197 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((520495195595 : Dyadic) * half ^ 41),
        ((959175671009 : Dyadic) * half ^ 41)⟩,
       ⟨((92055348573 : Dyadic) * half ^ 38),
        ((29028029883 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-92055348573 : Dyadic) * half ^ 38),
        ((-29028029883 : Dyadic) * half ^ 41)⟩,
       ⟨((-520495195595 : Dyadic) * half ^ 41),
        ((-959175671009 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((29841918511 : Dyadic) * half ^ 38),
        ((-359284963197 : Dyadic) * half ^ 40)⟩,
       ⟨((881843467555 : Dyadic) * half ^ 41),
        ((-395847770161 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word18Step51 :
    word18Chunk51.foldl (fun acc a => a.applyPacked acc)
      word18State51 = word18State52 := by decide +kernel

private def word18Chunk52 : List Letter := [.s, .t, .h, .s, .t, .h]
private def word18State53 : PackedMat2 :=
    ⟨⟨⟨((3504960060597 : Dyadic) * half ^ 42),
        ((157876871279 : Dyadic) * half ^ 40)⟩,
       ⟨((755162356863 : Dyadic) * half ^ 42),
        ((-267008846519 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-235134276297 : Dyadic) * half ^ 42),
        ((166265041259 : Dyadic) * half ^ 42)⟩,
       ⟨((1582603621565 : Dyadic) * half ^ 42),
        ((-1119069752739 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((235134276297 : Dyadic) * half ^ 42),
        ((-166265041259 : Dyadic) * half ^ 42)⟩,
       ⟨((1582603621565 : Dyadic) * half ^ 42),
        ((-1119069752739 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((3504960060597 : Dyadic) * half ^ 42),
        ((157876871279 : Dyadic) * half ^ 40)⟩,
       ⟨((-755162356863 : Dyadic) * half ^ 42),
        ((267008846519 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word18Step52 :
    word18Chunk52.foldl (fun acc a => a.applyPacked acc)
      word18State52 = word18State53 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word18_check : check word18 18 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word18 = word18State53.toMatrix := by
    unfold evalRingPacked
    change ((
      word18Chunk0 ++ word18Chunk1 ++ word18Chunk2 ++ word18Chunk3 ++
      word18Chunk4 ++ word18Chunk5 ++ word18Chunk6 ++ word18Chunk7 ++
      word18Chunk8 ++ word18Chunk9 ++ word18Chunk10 ++ word18Chunk11 ++
      word18Chunk12 ++ word18Chunk13 ++ word18Chunk14 ++ word18Chunk15 ++
      word18Chunk16 ++ word18Chunk17 ++ word18Chunk18 ++ word18Chunk19 ++
      word18Chunk20 ++ word18Chunk21 ++ word18Chunk22 ++ word18Chunk23 ++
      word18Chunk24 ++ word18Chunk25 ++ word18Chunk26 ++ word18Chunk27 ++
      word18Chunk28 ++ word18Chunk29 ++ word18Chunk30 ++ word18Chunk31 ++
      word18Chunk32 ++ word18Chunk33 ++ word18Chunk34 ++ word18Chunk35 ++
      word18Chunk36 ++ word18Chunk37 ++ word18Chunk38 ++ word18Chunk39 ++
      word18Chunk40 ++ word18Chunk41 ++ word18Chunk42 ++ word18Chunk43 ++
      word18Chunk44 ++ word18Chunk45 ++ word18Chunk46 ++ word18Chunk47 ++
      word18Chunk48 ++ word18Chunk49 ++ word18Chunk50 ++ word18Chunk51 ++
      word18Chunk52
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word18Step0, word18Step1, word18Step2, word18Step3, word18Step4,
      word18Step5, word18Step6, word18Step7, word18Step8, word18Step9,
      word18Step10, word18Step11, word18Step12, word18Step13, word18Step14,
      word18Step15, word18Step16, word18Step17, word18Step18, word18Step19,
      word18Step20, word18Step21, word18Step22, word18Step23, word18Step24,
      word18Step25, word18Step26, word18Step27, word18Step28, word18Step29,
      word18Step30, word18Step31, word18Step32, word18Step33, word18Step34,
      word18Step35, word18Step36, word18Step37, word18Step38, word18Step39,
      word18Step40, word18Step41, word18Step42, word18Step43, word18Step44,
      word18Step45, word18Step46, word18Step47, word18Step48, word18Step49,
      word18Step50, word18Step51, word18Step52]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
