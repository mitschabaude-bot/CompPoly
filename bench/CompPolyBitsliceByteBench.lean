/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CompPoly Contributors
-/
module
import CompPoly.Fields.Binary.AdditiveNTT.Bitsliced.Layout
/-! # Byte-table Four-Russians screening -/
public section
open AdditiveNTT.Bitsliced BF64
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private abbrev Tables := {b : ByteArray // b.size = 16384}

@[inline] private def read (s : @& Tables) (i : USize) (hi : i.toNat ≤ 16376) : UInt64 :=
  have hp : (i + 4).toNat = i.toNat + 4 := by
    rw [Native.add_toNat _ _ (by rw [Native.small 4 (by decide)]; omega),
      Native.small 4 (by decide)]
  (s.val.ugetUInt32LE i (by rw [s.property]; omega)).toUInt64 |||
    ((s.val.ugetUInt32LE (i + 4) (by rw [s.property, hp]; omega)).toUInt64 <<< 32)

@[inline] private def write (s : Tables) (i : USize) (hi : i.toNat ≤ 16376)
    (v : UInt64) : Tables :=
  have hp : (i + 4).toNat = i.toNat + 4 := by
    rw [Native.add_toNat _ _ (by rw [Native.small 4 (by decide)]; omega),
      Native.small 4 (by decide)]
  let b := s.val.usetUInt32LE i v.toUInt32 (by rw [s.property]; omega)
  let c := b.usetUInt32LE (i + 4) (v >>> 32).toUInt32 (by
    simp only [b, ByteArray.size_usetUInt32LE, hp, s.property]; omega)
  ⟨c, by simp only [c, b, ByteArray.size_usetUInt32LE, s.property]⟩

private theorem slot (base off : USize) (hb : base.toNat ≤ 14336)
    (ho : off.toNat ≤ 2040) : (base + off).toNat ≤ 16376 := by
  rw [Native.add_toNat base off (by omega)]
  omega

@[noinline] private def fillByte (s : Tables) (base : USize) (hb : base.toNat ≤ 14336)
    (a b c d e f g h : UInt64) : Tables :=
  let s := write s base (by omega) 0
  let v := a
  let s := write s (base + 8)
    (slot base 8 hb (by rw [Native.small 8 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 24)
    (slot base 24 hb (by rw [Native.small 24 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 16)
    (slot base 16 hb (by rw [Native.small 16 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 48)
    (slot base 48 hb (by rw [Native.small 48 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 56)
    (slot base 56 hb (by rw [Native.small 56 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 40)
    (slot base 40 hb (by rw [Native.small 40 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 32)
    (slot base 32 hb (by rw [Native.small 32 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 96)
    (slot base 96 hb (by rw [Native.small 96 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 104)
    (slot base 104 hb (by rw [Native.small 104 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 120)
    (slot base 120 hb (by rw [Native.small 120 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 112)
    (slot base 112 hb (by rw [Native.small 112 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 80)
    (slot base 80 hb (by rw [Native.small 80 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 88)
    (slot base 88 hb (by rw [Native.small 88 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 72)
    (slot base 72 hb (by rw [Native.small 72 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 64)
    (slot base 64 hb (by rw [Native.small 64 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 192)
    (slot base 192 hb (by rw [Native.small 192 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 200)
    (slot base 200 hb (by rw [Native.small 200 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 216)
    (slot base 216 hb (by rw [Native.small 216 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 208)
    (slot base 208 hb (by rw [Native.small 208 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 240)
    (slot base 240 hb (by rw [Native.small 240 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 248)
    (slot base 248 hb (by rw [Native.small 248 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 232)
    (slot base 232 hb (by rw [Native.small 232 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 224)
    (slot base 224 hb (by rw [Native.small 224 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 160)
    (slot base 160 hb (by rw [Native.small 160 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 168)
    (slot base 168 hb (by rw [Native.small 168 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 184)
    (slot base 184 hb (by rw [Native.small 184 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 176)
    (slot base 176 hb (by rw [Native.small 176 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 144)
    (slot base 144 hb (by rw [Native.small 144 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 152)
    (slot base 152 hb (by rw [Native.small 152 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 136)
    (slot base 136 hb (by rw [Native.small 136 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 128)
    (slot base 128 hb (by rw [Native.small 128 (by decide)]; omega)) v
  let v := v ^^^ f
  let s := write s (base + 384)
    (slot base 384 hb (by rw [Native.small 384 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 392)
    (slot base 392 hb (by rw [Native.small 392 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 408)
    (slot base 408 hb (by rw [Native.small 408 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 400)
    (slot base 400 hb (by rw [Native.small 400 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 432)
    (slot base 432 hb (by rw [Native.small 432 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 440)
    (slot base 440 hb (by rw [Native.small 440 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 424)
    (slot base 424 hb (by rw [Native.small 424 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 416)
    (slot base 416 hb (by rw [Native.small 416 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 480)
    (slot base 480 hb (by rw [Native.small 480 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 488)
    (slot base 488 hb (by rw [Native.small 488 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 504)
    (slot base 504 hb (by rw [Native.small 504 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 496)
    (slot base 496 hb (by rw [Native.small 496 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 464)
    (slot base 464 hb (by rw [Native.small 464 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 472)
    (slot base 472 hb (by rw [Native.small 472 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 456)
    (slot base 456 hb (by rw [Native.small 456 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 448)
    (slot base 448 hb (by rw [Native.small 448 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 320)
    (slot base 320 hb (by rw [Native.small 320 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 328)
    (slot base 328 hb (by rw [Native.small 328 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 344)
    (slot base 344 hb (by rw [Native.small 344 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 336)
    (slot base 336 hb (by rw [Native.small 336 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 368)
    (slot base 368 hb (by rw [Native.small 368 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 376)
    (slot base 376 hb (by rw [Native.small 376 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 360)
    (slot base 360 hb (by rw [Native.small 360 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 352)
    (slot base 352 hb (by rw [Native.small 352 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 288)
    (slot base 288 hb (by rw [Native.small 288 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 296)
    (slot base 296 hb (by rw [Native.small 296 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 312)
    (slot base 312 hb (by rw [Native.small 312 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 304)
    (slot base 304 hb (by rw [Native.small 304 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 272)
    (slot base 272 hb (by rw [Native.small 272 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 280)
    (slot base 280 hb (by rw [Native.small 280 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 264)
    (slot base 264 hb (by rw [Native.small 264 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 256)
    (slot base 256 hb (by rw [Native.small 256 (by decide)]; omega)) v
  let v := v ^^^ g
  let s := write s (base + 768)
    (slot base 768 hb (by rw [Native.small 768 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 776)
    (slot base 776 hb (by rw [Native.small 776 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 792)
    (slot base 792 hb (by rw [Native.small 792 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 784)
    (slot base 784 hb (by rw [Native.small 784 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 816)
    (slot base 816 hb (by rw [Native.small 816 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 824)
    (slot base 824 hb (by rw [Native.small 824 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 808)
    (slot base 808 hb (by rw [Native.small 808 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 800)
    (slot base 800 hb (by rw [Native.small 800 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 864)
    (slot base 864 hb (by rw [Native.small 864 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 872)
    (slot base 872 hb (by rw [Native.small 872 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 888)
    (slot base 888 hb (by rw [Native.small 888 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 880)
    (slot base 880 hb (by rw [Native.small 880 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 848)
    (slot base 848 hb (by rw [Native.small 848 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 856)
    (slot base 856 hb (by rw [Native.small 856 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 840)
    (slot base 840 hb (by rw [Native.small 840 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 832)
    (slot base 832 hb (by rw [Native.small 832 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 960)
    (slot base 960 hb (by rw [Native.small 960 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 968)
    (slot base 968 hb (by rw [Native.small 968 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 984)
    (slot base 984 hb (by rw [Native.small 984 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 976)
    (slot base 976 hb (by rw [Native.small 976 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1008)
    (slot base 1008 hb (by rw [Native.small 1008 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1016)
    (slot base 1016 hb (by rw [Native.small 1016 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1000)
    (slot base 1000 hb (by rw [Native.small 1000 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 992)
    (slot base 992 hb (by rw [Native.small 992 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 928)
    (slot base 928 hb (by rw [Native.small 928 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 936)
    (slot base 936 hb (by rw [Native.small 936 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 952)
    (slot base 952 hb (by rw [Native.small 952 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 944)
    (slot base 944 hb (by rw [Native.small 944 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 912)
    (slot base 912 hb (by rw [Native.small 912 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 920)
    (slot base 920 hb (by rw [Native.small 920 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 904)
    (slot base 904 hb (by rw [Native.small 904 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 896)
    (slot base 896 hb (by rw [Native.small 896 (by decide)]; omega)) v
  let v := v ^^^ f
  let s := write s (base + 640)
    (slot base 640 hb (by rw [Native.small 640 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 648)
    (slot base 648 hb (by rw [Native.small 648 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 664)
    (slot base 664 hb (by rw [Native.small 664 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 656)
    (slot base 656 hb (by rw [Native.small 656 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 688)
    (slot base 688 hb (by rw [Native.small 688 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 696)
    (slot base 696 hb (by rw [Native.small 696 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 680)
    (slot base 680 hb (by rw [Native.small 680 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 672)
    (slot base 672 hb (by rw [Native.small 672 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 736)
    (slot base 736 hb (by rw [Native.small 736 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 744)
    (slot base 744 hb (by rw [Native.small 744 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 760)
    (slot base 760 hb (by rw [Native.small 760 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 752)
    (slot base 752 hb (by rw [Native.small 752 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 720)
    (slot base 720 hb (by rw [Native.small 720 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 728)
    (slot base 728 hb (by rw [Native.small 728 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 712)
    (slot base 712 hb (by rw [Native.small 712 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 704)
    (slot base 704 hb (by rw [Native.small 704 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 576)
    (slot base 576 hb (by rw [Native.small 576 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 584)
    (slot base 584 hb (by rw [Native.small 584 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 600)
    (slot base 600 hb (by rw [Native.small 600 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 592)
    (slot base 592 hb (by rw [Native.small 592 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 624)
    (slot base 624 hb (by rw [Native.small 624 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 632)
    (slot base 632 hb (by rw [Native.small 632 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 616)
    (slot base 616 hb (by rw [Native.small 616 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 608)
    (slot base 608 hb (by rw [Native.small 608 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 544)
    (slot base 544 hb (by rw [Native.small 544 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 552)
    (slot base 552 hb (by rw [Native.small 552 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 568)
    (slot base 568 hb (by rw [Native.small 568 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 560)
    (slot base 560 hb (by rw [Native.small 560 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 528)
    (slot base 528 hb (by rw [Native.small 528 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 536)
    (slot base 536 hb (by rw [Native.small 536 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 520)
    (slot base 520 hb (by rw [Native.small 520 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 512)
    (slot base 512 hb (by rw [Native.small 512 (by decide)]; omega)) v
  let v := v ^^^ h
  let s := write s (base + 1536)
    (slot base 1536 hb (by rw [Native.small 1536 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1544)
    (slot base 1544 hb (by rw [Native.small 1544 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1560)
    (slot base 1560 hb (by rw [Native.small 1560 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1552)
    (slot base 1552 hb (by rw [Native.small 1552 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1584)
    (slot base 1584 hb (by rw [Native.small 1584 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1592)
    (slot base 1592 hb (by rw [Native.small 1592 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1576)
    (slot base 1576 hb (by rw [Native.small 1576 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1568)
    (slot base 1568 hb (by rw [Native.small 1568 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1632)
    (slot base 1632 hb (by rw [Native.small 1632 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1640)
    (slot base 1640 hb (by rw [Native.small 1640 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1656)
    (slot base 1656 hb (by rw [Native.small 1656 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1648)
    (slot base 1648 hb (by rw [Native.small 1648 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1616)
    (slot base 1616 hb (by rw [Native.small 1616 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1624)
    (slot base 1624 hb (by rw [Native.small 1624 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1608)
    (slot base 1608 hb (by rw [Native.small 1608 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1600)
    (slot base 1600 hb (by rw [Native.small 1600 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 1728)
    (slot base 1728 hb (by rw [Native.small 1728 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1736)
    (slot base 1736 hb (by rw [Native.small 1736 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1752)
    (slot base 1752 hb (by rw [Native.small 1752 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1744)
    (slot base 1744 hb (by rw [Native.small 1744 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1776)
    (slot base 1776 hb (by rw [Native.small 1776 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1784)
    (slot base 1784 hb (by rw [Native.small 1784 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1768)
    (slot base 1768 hb (by rw [Native.small 1768 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1760)
    (slot base 1760 hb (by rw [Native.small 1760 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1696)
    (slot base 1696 hb (by rw [Native.small 1696 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1704)
    (slot base 1704 hb (by rw [Native.small 1704 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1720)
    (slot base 1720 hb (by rw [Native.small 1720 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1712)
    (slot base 1712 hb (by rw [Native.small 1712 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1680)
    (slot base 1680 hb (by rw [Native.small 1680 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1688)
    (slot base 1688 hb (by rw [Native.small 1688 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1672)
    (slot base 1672 hb (by rw [Native.small 1672 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1664)
    (slot base 1664 hb (by rw [Native.small 1664 (by decide)]; omega)) v
  let v := v ^^^ f
  let s := write s (base + 1920)
    (slot base 1920 hb (by rw [Native.small 1920 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1928)
    (slot base 1928 hb (by rw [Native.small 1928 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1944)
    (slot base 1944 hb (by rw [Native.small 1944 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1936)
    (slot base 1936 hb (by rw [Native.small 1936 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1968)
    (slot base 1968 hb (by rw [Native.small 1968 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1976)
    (slot base 1976 hb (by rw [Native.small 1976 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1960)
    (slot base 1960 hb (by rw [Native.small 1960 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1952)
    (slot base 1952 hb (by rw [Native.small 1952 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 2016)
    (slot base 2016 hb (by rw [Native.small 2016 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 2024)
    (slot base 2024 hb (by rw [Native.small 2024 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 2040)
    (slot base 2040 hb (by rw [Native.small 2040 (by decide)])) v
  let v := v ^^^ a
  let s := write s (base + 2032)
    (slot base 2032 hb (by rw [Native.small 2032 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 2000)
    (slot base 2000 hb (by rw [Native.small 2000 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 2008)
    (slot base 2008 hb (by rw [Native.small 2008 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1992)
    (slot base 1992 hb (by rw [Native.small 1992 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1984)
    (slot base 1984 hb (by rw [Native.small 1984 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 1856)
    (slot base 1856 hb (by rw [Native.small 1856 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1864)
    (slot base 1864 hb (by rw [Native.small 1864 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1880)
    (slot base 1880 hb (by rw [Native.small 1880 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1872)
    (slot base 1872 hb (by rw [Native.small 1872 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1904)
    (slot base 1904 hb (by rw [Native.small 1904 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1912)
    (slot base 1912 hb (by rw [Native.small 1912 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1896)
    (slot base 1896 hb (by rw [Native.small 1896 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1888)
    (slot base 1888 hb (by rw [Native.small 1888 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1824)
    (slot base 1824 hb (by rw [Native.small 1824 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1832)
    (slot base 1832 hb (by rw [Native.small 1832 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1848)
    (slot base 1848 hb (by rw [Native.small 1848 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1840)
    (slot base 1840 hb (by rw [Native.small 1840 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1808)
    (slot base 1808 hb (by rw [Native.small 1808 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1816)
    (slot base 1816 hb (by rw [Native.small 1816 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1800)
    (slot base 1800 hb (by rw [Native.small 1800 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1792)
    (slot base 1792 hb (by rw [Native.small 1792 (by decide)]; omega)) v
  let v := v ^^^ g
  let s := write s (base + 1280)
    (slot base 1280 hb (by rw [Native.small 1280 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1288)
    (slot base 1288 hb (by rw [Native.small 1288 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1304)
    (slot base 1304 hb (by rw [Native.small 1304 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1296)
    (slot base 1296 hb (by rw [Native.small 1296 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1328)
    (slot base 1328 hb (by rw [Native.small 1328 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1336)
    (slot base 1336 hb (by rw [Native.small 1336 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1320)
    (slot base 1320 hb (by rw [Native.small 1320 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1312)
    (slot base 1312 hb (by rw [Native.small 1312 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1376)
    (slot base 1376 hb (by rw [Native.small 1376 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1384)
    (slot base 1384 hb (by rw [Native.small 1384 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1400)
    (slot base 1400 hb (by rw [Native.small 1400 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1392)
    (slot base 1392 hb (by rw [Native.small 1392 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1360)
    (slot base 1360 hb (by rw [Native.small 1360 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1368)
    (slot base 1368 hb (by rw [Native.small 1368 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1352)
    (slot base 1352 hb (by rw [Native.small 1352 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1344)
    (slot base 1344 hb (by rw [Native.small 1344 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 1472)
    (slot base 1472 hb (by rw [Native.small 1472 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1480)
    (slot base 1480 hb (by rw [Native.small 1480 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1496)
    (slot base 1496 hb (by rw [Native.small 1496 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1488)
    (slot base 1488 hb (by rw [Native.small 1488 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1520)
    (slot base 1520 hb (by rw [Native.small 1520 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1528)
    (slot base 1528 hb (by rw [Native.small 1528 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1512)
    (slot base 1512 hb (by rw [Native.small 1512 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1504)
    (slot base 1504 hb (by rw [Native.small 1504 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1440)
    (slot base 1440 hb (by rw [Native.small 1440 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1448)
    (slot base 1448 hb (by rw [Native.small 1448 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1464)
    (slot base 1464 hb (by rw [Native.small 1464 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1456)
    (slot base 1456 hb (by rw [Native.small 1456 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1424)
    (slot base 1424 hb (by rw [Native.small 1424 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1432)
    (slot base 1432 hb (by rw [Native.small 1432 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1416)
    (slot base 1416 hb (by rw [Native.small 1416 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1408)
    (slot base 1408 hb (by rw [Native.small 1408 (by decide)]; omega)) v
  let v := v ^^^ f
  let s := write s (base + 1152)
    (slot base 1152 hb (by rw [Native.small 1152 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1160)
    (slot base 1160 hb (by rw [Native.small 1160 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1176)
    (slot base 1176 hb (by rw [Native.small 1176 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1168)
    (slot base 1168 hb (by rw [Native.small 1168 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1200)
    (slot base 1200 hb (by rw [Native.small 1200 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1208)
    (slot base 1208 hb (by rw [Native.small 1208 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1192)
    (slot base 1192 hb (by rw [Native.small 1192 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1184)
    (slot base 1184 hb (by rw [Native.small 1184 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1248)
    (slot base 1248 hb (by rw [Native.small 1248 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1256)
    (slot base 1256 hb (by rw [Native.small 1256 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1272)
    (slot base 1272 hb (by rw [Native.small 1272 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1264)
    (slot base 1264 hb (by rw [Native.small 1264 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1232)
    (slot base 1232 hb (by rw [Native.small 1232 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1240)
    (slot base 1240 hb (by rw [Native.small 1240 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1224)
    (slot base 1224 hb (by rw [Native.small 1224 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1216)
    (slot base 1216 hb (by rw [Native.small 1216 (by decide)]; omega)) v
  let v := v ^^^ e
  let s := write s (base + 1088)
    (slot base 1088 hb (by rw [Native.small 1088 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1096)
    (slot base 1096 hb (by rw [Native.small 1096 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1112)
    (slot base 1112 hb (by rw [Native.small 1112 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1104)
    (slot base 1104 hb (by rw [Native.small 1104 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1136)
    (slot base 1136 hb (by rw [Native.small 1136 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1144)
    (slot base 1144 hb (by rw [Native.small 1144 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1128)
    (slot base 1128 hb (by rw [Native.small 1128 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1120)
    (slot base 1120 hb (by rw [Native.small 1120 (by decide)]; omega)) v
  let v := v ^^^ d
  let s := write s (base + 1056)
    (slot base 1056 hb (by rw [Native.small 1056 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1064)
    (slot base 1064 hb (by rw [Native.small 1064 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1080)
    (slot base 1080 hb (by rw [Native.small 1080 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1072)
    (slot base 1072 hb (by rw [Native.small 1072 (by decide)]; omega)) v
  let v := v ^^^ c
  let s := write s (base + 1040)
    (slot base 1040 hb (by rw [Native.small 1040 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1048)
    (slot base 1048 hb (by rw [Native.small 1048 (by decide)]; omega)) v
  let v := v ^^^ b
  let s := write s (base + 1032)
    (slot base 1032 hb (by rw [Native.small 1032 (by decide)]; omega)) v
  let v := v ^^^ a
  let s := write s (base + 1024)
    (slot base 1024 hb (by rw [Native.small 1024 (by decide)]; omega)) v
  s

@[noinline] private def prepare (s : Tables) (a : Block) : Tables :=
  let s := fillByte s 0 (by rw [Native.small 0 (by decide)]; omega)
    a.w0 a.w1 a.w2 a.w3 a.w4 a.w5 a.w6 a.w7
  let s := fillByte s 2048 (by rw [Native.small 2048 (by decide)]; omega)
    a.w8 a.w9 a.w10 a.w11 a.w12 a.w13 a.w14 a.w15
  let s := fillByte s 4096 (by rw [Native.small 4096 (by decide)]; omega)
    a.w16 a.w17 a.w18 a.w19 a.w20 a.w21 a.w22 a.w23
  let s := fillByte s 6144 (by rw [Native.small 6144 (by decide)]; omega)
    a.w24 a.w25 a.w26 a.w27 a.w28 a.w29 a.w30 a.w31
  let s := fillByte s 8192 (by rw [Native.small 8192 (by decide)]; omega)
    a.w32 a.w33 a.w34 a.w35 a.w36 a.w37 a.w38 a.w39
  let s := fillByte s 10240 (by rw [Native.small 10240 (by decide)]; omega)
    a.w40 a.w41 a.w42 a.w43 a.w44 a.w45 a.w46 a.w47
  let s := fillByte s 12288 (by rw [Native.small 12288 (by decide)]; omega)
    a.w48 a.w49 a.w50 a.w51 a.w52 a.w53 a.w54 a.w55
  let s := fillByte s 14336 (by rw [Native.small 14336 (by decide)])
    a.w56 a.w57 a.w58 a.w59 a.w60 a.w61 a.w62 a.w63
  s

private theorem byteOffset (g : USize) (hg : g.toNat < 8) (v : UInt64) :
    (g * 2048 + (v &&& 255).toUSize * 8).toNat ≤ 16376 := by
  have hv : (v &&& 255).toNat < 256 := by
    rw [UInt64.toNat_and]
    exact Nat.and_lt_two_pow _ (by decide : (255 : UInt64).toNat < 2 ^ 8)
  have hc : (v &&& 255).toUSize.toNat = (v &&& 255).toNat := by
    rw [UInt64.toNat_toUSize, Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) USize.le_size)]
  have hs : 4294967296 ≤ 2 ^ System.Platform.numBits := USize.le_size
  have h1 : g.toNat * 2048 < 2 ^ System.Platform.numBits := lt_of_lt_of_le (by omega) hs
  have h2 : (v &&& 255).toNat * 8 < 2 ^ System.Platform.numBits := lt_of_lt_of_le (by omega) hs
  simp only [USize.toNat_add, USize.toNat_mul, Native.small 2048 (by decide),
    Native.small 8 (by decide), hc, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (by omega) hs)]
  omega

@[inline] private def lookup (s : @& Tables) (g : USize) (hg : g.toNat < 8)
    (v : UInt64) : UInt64 :=
  read s (g * 2048 + (v &&& 255).toUSize * 8) (byteOffset g hg v)

@[noinline] private def dot (s : @& Tables) (m : UInt64) : UInt64 :=
  lookup s 0 (by rw [Native.small 0 (by decide)]; omega) (m >>> 0) ^^^
  lookup s 1 (by rw [Native.small 1 (by decide)]; omega) (m >>> 8) ^^^
  lookup s 2 (by rw [Native.small 2 (by decide)]; omega) (m >>> 16) ^^^
  lookup s 3 (by rw [Native.small 3 (by decide)]; omega) (m >>> 24) ^^^
  lookup s 4 (by rw [Native.small 4 (by decide)]; omega) (m >>> 32) ^^^
  lookup s 5 (by rw [Native.small 5 (by decide)]; omega) (m >>> 40) ^^^
  lookup s 6 (by rw [Native.small 6 (by decide)]; omega) (m >>> 48) ^^^
  lookup s 7 (by rw [Native.small 7 (by decide)]; omega) (m >>> 56)

@[noinline] private def apply (s : @& Tables) (m : @& Block) : Block :=
  ⟨dot s m.w0,
    dot s m.w1,
    dot s m.w2,
    dot s m.w3,
    dot s m.w4,
    dot s m.w5,
    dot s m.w6,
    dot s m.w7,
    dot s m.w8,
    dot s m.w9,
    dot s m.w10,
    dot s m.w11,
    dot s m.w12,
    dot s m.w13,
    dot s m.w14,
    dot s m.w15,
    dot s m.w16,
    dot s m.w17,
    dot s m.w18,
    dot s m.w19,
    dot s m.w20,
    dot s m.w21,
    dot s m.w22,
    dot s m.w23,
    dot s m.w24,
    dot s m.w25,
    dot s m.w26,
    dot s m.w27,
    dot s m.w28,
    dot s m.w29,
    dot s m.w30,
    dot s m.w31,
    dot s m.w32,
    dot s m.w33,
    dot s m.w34,
    dot s m.w35,
    dot s m.w36,
    dot s m.w37,
    dot s m.w38,
    dot s m.w39,
    dot s m.w40,
    dot s m.w41,
    dot s m.w42,
    dot s m.w43,
    dot s m.w44,
    dot s m.w45,
    dot s m.w46,
    dot s m.w47,
    dot s m.w48,
    dot s m.w49,
    dot s m.w50,
    dot s m.w51,
    dot s m.w52,
    dot s m.w53,
    dot s m.w54,
    dot s m.w55,
    dot s m.w56,
    dot s m.w57,
    dot s m.w58,
    dot s m.w59,
    dot s m.w60,
    dot s m.w61,
    dot s m.w62,
    dot s m.w63⟩

@[noinline] private def prepareChain : Nat → Block → Tables → Tables
  | 0, _, s => s
  | n + 1, a, s => prepareChain n a (prepare s a)

@[noinline] private def applyChain : Nat → Tables → Block → Block
  | 0, _, m => m
  | n + 1, s, m => applyChain n s (apply s m)

@[noinline] private def chain : Nat → Block → Tables → Block → Block
  | 0, _, _, a => a
  | n + 1, m, s, a =>
    let s := prepare s a
    chain n m s (apply s m)

private def seed (i : Nat) : UInt64 :=
  0x0123456789abcdef ^^^ ((UInt64.ofNat i + 1) * 0x9e3779b97f4a7c15)

/-- Check byte tables against field multiplication, or measure dependent chains. -/
def main (args : List String) : IO Unit := do
  let [mode, part, rawN] := args | throw <| IO.userError "expected mode part count"
  let some n := rawN.toNat? | throw <| IO.userError "invalid count"
  let a := Block.ofFn fun i => seed i.val
  let p := transpose a
  let m := matrix (seed 67)
  let empty : Tables := ⟨ByteArray.zeros 16384, ByteArray.size_zeros _⟩
  let s := prepare empty p
  if mode == "check" then
    for t in [0, 1, 2, 0x8000000000000000, seed 67] do
      let out := transpose (apply s (matrix t))
      for i in List.finRange 64 do
        unless out.get i == (Word.mulMasked ⟨t⟩ ⟨a.get i⟩).val do
          throw <| IO.userError "byte table product mismatch"
    IO.println "320 byte-table lane products passed"
  else
    let stdout ← IO.getStdout
    let stdin ← IO.getStdin
    stdout.putStrLn "begin 0"
    stdout.flush
    discard <| stdin.getLine
    let start ← IO.monoNanosNow
    let sink ← match part with
      | "prepare" =>
        pure (read (prepareChain n p s) 8 (by rw [Native.small 8 (by decide)]; omega))
      | "apply" => pure (applyChain n s m).w0
      | "combined" => pure (chain n m s p).w0
      | _ => throw <| IO.userError "invalid part"
    let stop ← IO.monoNanosNow
    stdout.putStrLn s!"end {stop-start}"
    stdout.flush
    discard <| stdin.getLine
    IO.println s!"sink {sink}"
