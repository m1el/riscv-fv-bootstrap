/- AUTO-GENERATED from bare/hex1.elf by tools/gen_decode1.py. Do not edit.
   One kernel-checked decode fact per core1 instruction. -/
import Hex1.RefineBase
open Rv64i

namespace Hex1.Refine

set_option maxRecDepth 8000

theorem coreBytes_len : Image1.coreBytes.length = 724 := by decide

/-- `   0: 00070e13  addi x28,x14,0` -/
theorem dec_0 : Rv64i.decode (wordAt1 0) = Rv64i.Instr.addi 28 14 (BitVec.ofNat 12 0) := by decide
/-- `   4: 7ff70e93  addi x29,x14,2047` -/
theorem dec_4 : Rv64i.decode (wordAt1 4) = Rv64i.Instr.addi 29 14 (BitVec.ofNat 12 2047) := by decide
/-- `   8: 001e8e93  addi x29,x29,1` -/
theorem dec_8 : Rv64i.decode (wordAt1 8) = Rv64i.Instr.addi 29 29 (BitVec.ofNat 12 1) := by decide
/-- `  12: fff00f13  addi x30,x0,-1` -/
theorem dec_12 : Rv64i.decode (wordAt1 12) = Rv64i.Instr.addi 30 0 (BitVec.ofNat 12 4095) := by decide
/-- `  16: 01ee3023  sd x30,0(x28)` -/
theorem dec_16 : Rv64i.decode (wordAt1 16) = Rv64i.Instr.sd 28 30 (BitVec.ofNat 12 0) := by decide
/-- `  20: 008e0e13  addi x28,x28,8` -/
theorem dec_20 : Rv64i.decode (wordAt1 20) = Rv64i.Instr.addi 28 28 (BitVec.ofNat 12 8) := by decide
/-- `  24: ffde4ce3  blt x28,x29,800000a0 <core1+0x10>` -/
theorem dec_24 : Rv64i.decode (wordAt1 24) = Rv64i.Instr.blt 28 29 (BitVec.ofNat 13 8184) := by decide
/-- `  28: 00000293  addi x5,x0,0` -/
theorem dec_28 : Rv64i.decode (wordAt1 28) = Rv64i.Instr.addi 5 0 (BitVec.ofNat 12 0) := by decide
/-- `  32: 00000313  addi x6,x0,0` -/
theorem dec_32 : Rv64i.decode (wordAt1 32) = Rv64i.Instr.addi 6 0 (BitVec.ofNat 12 0) := by decide
/-- `  36: 14b2f263  bgeu x5,x11,800001f8 <core1+0x168>` -/
theorem dec_36 : Rv64i.decode (wordAt1 36) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 324) := by decide
/-- `  40: 00550e33  add x28,x10,x5` -/
theorem dec_40 : Rv64i.decode (wordAt1 40) = Rv64i.Instr.add 28 10 5 := by decide
/-- `  44: 000e4383  lbu x7,0(x28)` -/
theorem dec_44 : Rv64i.decode (wordAt1 44) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- `  48: 00128293  addi x5,x5,1` -/
theorem dec_48 : Rv64i.decode (wordAt1 48) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- `  52: 02300e13  addi x28,x0,35` -/
theorem dec_52 : Rv64i.decode (wordAt1 52) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 35) := by decide
/-- `  56: 11c38a63  beq x7,x28,800001dc <core1+0x14c>` -/
theorem dec_56 : Rv64i.decode (wordAt1 56) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 276) := by decide
/-- `  60: 03b00e13  addi x28,x0,59` -/
theorem dec_60 : Rv64i.decode (wordAt1 60) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 59) := by decide
/-- `  64: 11c38663  beq x7,x28,800001dc <core1+0x14c>` -/
theorem dec_64 : Rv64i.decode (wordAt1 64) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 268) := by decide
/-- `  68: 00a00e13  addi x28,x0,10` -/
theorem dec_68 : Rv64i.decode (wordAt1 68) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 10) := by decide
/-- `  72: fdc38ee3  beq x7,x28,800000b4 <core1+0x24>` -/
theorem dec_72 : Rv64i.decode (wordAt1 72) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 8156) := by decide
/-- `  76: 02000e13  addi x28,x0,32` -/
theorem dec_76 : Rv64i.decode (wordAt1 76) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 32) := by decide
/-- `  80: fdc38ae3  beq x7,x28,800000b4 <core1+0x24>` -/
theorem dec_80 : Rv64i.decode (wordAt1 80) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 8148) := by decide
/-- `  84: 05f00e13  addi x28,x0,95` -/
theorem dec_84 : Rv64i.decode (wordAt1 84) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 95) := by decide
/-- `  88: fdc386e3  beq x7,x28,800000b4 <core1+0x24>` -/
theorem dec_88 : Rv64i.decode (wordAt1 88) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 8140) := by decide
/-- `  92: 03a00e13  addi x28,x0,58` -/
theorem dec_92 : Rv64i.decode (wordAt1 92) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- `  96: 0bc38463  beq x7,x28,80000198 <core1+0x108>` -/
theorem dec_96 : Rv64i.decode (wordAt1 96) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 168) := by decide
/-- ` 100: 02500e13  addi x28,x0,37` -/
theorem dec_100 : Rv64i.decode (wordAt1 100) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 37) := by decide
/-- ` 104: 0dc38463  beq x7,x28,800001c0 <core1+0x130>` -/
theorem dec_104 : Rv64i.decode (wordAt1 104) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 200) := by decide
/-- ` 108: 03000e13  addi x28,x0,48` -/
theorem dec_108 : Rv64i.decode (wordAt1 108) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 48) := by decide
/-- ` 112: 23c3ca63  blt x7,x28,80000334 <core1+0x2a4>` -/
theorem dec_112 : Rv64i.decode (wordAt1 112) = Rv64i.Instr.blt 7 28 (BitVec.ofNat 13 564) := by decide
/-- ` 116: 03a00e13  addi x28,x0,58` -/
theorem dec_116 : Rv64i.decode (wordAt1 116) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- ` 120: 01c3d463  bge x7,x28,80000110 <core1+0x80>` -/
theorem dec_120 : Rv64i.decode (wordAt1 120) = Rv64i.Instr.bge 7 28 (BitVec.ofNat 13 8) := by decide
/-- ` 124: 0140006f  jal x0,80000120 <core1+0x90>` -/
theorem dec_124 : Rv64i.decode (wordAt1 124) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 20) := by decide
/-- ` 128: 04100e13  addi x28,x0,65` -/
theorem dec_128 : Rv64i.decode (wordAt1 128) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 65) := by decide
/-- ` 132: 23c3c063  blt x7,x28,80000334 <core1+0x2a4>` -/
theorem dec_132 : Rv64i.decode (wordAt1 132) = Rv64i.Instr.blt 7 28 (BitVec.ofNat 13 544) := by decide
/-- ` 136: 04700e13  addi x28,x0,71` -/
theorem dec_136 : Rv64i.decode (wordAt1 136) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 71) := by decide
/-- ` 140: 21c3dc63  bge x7,x28,80000334 <core1+0x2a4>` -/
theorem dec_140 : Rv64i.decode (wordAt1 140) = Rv64i.Instr.bge 7 28 (BitVec.ofNat 13 536) := by decide
/-- ` 144: 20b2f463  bgeu x5,x11,80000328 <core1+0x298>` -/
theorem dec_144 : Rv64i.decode (wordAt1 144) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 520) := by decide
/-- ` 148: 00550e33  add x28,x10,x5` -/
theorem dec_148 : Rv64i.decode (wordAt1 148) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 152: 000e4383  lbu x7,0(x28)` -/
theorem dec_152 : Rv64i.decode (wordAt1 152) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 156: 00128293  addi x5,x5,1` -/
theorem dec_156 : Rv64i.decode (wordAt1 156) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 160: 00a00e13  addi x28,x0,10` -/
theorem dec_160 : Rv64i.decode (wordAt1 160) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 10) := by decide
/-- ` 164: 1fc38463  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_164 : Rv64i.decode (wordAt1 164) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 488) := by decide
/-- ` 168: 02000e13  addi x28,x0,32` -/
theorem dec_168 : Rv64i.decode (wordAt1 168) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 32) := by decide
/-- ` 172: 1fc38063  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_172 : Rv64i.decode (wordAt1 172) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 480) := by decide
/-- ` 176: 05f00e13  addi x28,x0,95` -/
theorem dec_176 : Rv64i.decode (wordAt1 176) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 95) := by decide
/-- ` 180: 1dc38c63  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_180 : Rv64i.decode (wordAt1 180) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 472) := by decide
/-- ` 184: 02300e13  addi x28,x0,35` -/
theorem dec_184 : Rv64i.decode (wordAt1 184) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 35) := by decide
/-- ` 188: 1dc38863  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_188 : Rv64i.decode (wordAt1 188) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 464) := by decide
/-- ` 192: 03b00e13  addi x28,x0,59` -/
theorem dec_192 : Rv64i.decode (wordAt1 192) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 59) := by decide
/-- ` 196: 1dc38463  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_196 : Rv64i.decode (wordAt1 196) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 456) := by decide
/-- ` 200: 03a00e13  addi x28,x0,58` -/
theorem dec_200 : Rv64i.decode (wordAt1 200) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- ` 204: 1dc38063  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_204 : Rv64i.decode (wordAt1 204) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 448) := by decide
/-- ` 208: 02500e13  addi x28,x0,37` -/
theorem dec_208 : Rv64i.decode (wordAt1 208) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 37) := by decide
/-- ` 212: 1bc38c63  beq x7,x28,8000031c <core1+0x28c>` -/
theorem dec_212 : Rv64i.decode (wordAt1 212) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 440) := by decide
/-- ` 216: 03000e13  addi x28,x0,48` -/
theorem dec_216 : Rv64i.decode (wordAt1 216) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 48) := by decide
/-- ` 220: 1dc3c463  blt x7,x28,80000334 <core1+0x2a4>` -/
theorem dec_220 : Rv64i.decode (wordAt1 220) = Rv64i.Instr.blt 7 28 (BitVec.ofNat 13 456) := by decide
/-- ` 224: 03a00e13  addi x28,x0,58` -/
theorem dec_224 : Rv64i.decode (wordAt1 224) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- ` 228: 01c3d463  bge x7,x28,8000017c <core1+0xec>` -/
theorem dec_228 : Rv64i.decode (wordAt1 228) = Rv64i.Instr.bge 7 28 (BitVec.ofNat 13 8) := by decide
/-- ` 232: 0140006f  jal x0,8000018c <core1+0xfc>` -/
theorem dec_232 : Rv64i.decode (wordAt1 232) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 20) := by decide
/-- ` 236: 04100e13  addi x28,x0,65` -/
theorem dec_236 : Rv64i.decode (wordAt1 236) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 65) := by decide
/-- ` 240: 1bc3ca63  blt x7,x28,80000334 <core1+0x2a4>` -/
theorem dec_240 : Rv64i.decode (wordAt1 240) = Rv64i.Instr.blt 7 28 (BitVec.ofNat 13 436) := by decide
/-- ` 244: 04700e13  addi x28,x0,71` -/
theorem dec_244 : Rv64i.decode (wordAt1 244) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 71) := by decide
/-- ` 248: 1bc3d663  bge x7,x28,80000334 <core1+0x2a4>` -/
theorem dec_248 : Rv64i.decode (wordAt1 248) = Rv64i.Instr.bge 7 28 (BitVec.ofNat 13 428) := by decide
/-- ` 252: 18d37263  bgeu x6,x13,80000310 <core1+0x280>` -/
theorem dec_252 : Rv64i.decode (wordAt1 252) = Rv64i.Instr.bgeu 6 13 (BitVec.ofNat 13 388) := by decide
/-- ` 256: 00130313  addi x6,x6,1` -/
theorem dec_256 : Rv64i.decode (wordAt1 256) = Rv64i.Instr.addi 6 6 (BitVec.ofNat 12 1) := by decide
/-- ` 260: f21ff06f  jal x0,800000b4 <core1+0x24>` -/
theorem dec_260 : Rv64i.decode (wordAt1 260) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2096928) := by decide
/-- ` 264: 1cb2f063  bgeu x5,x11,80000358 <core1+0x2c8>` -/
theorem dec_264 : Rv64i.decode (wordAt1 264) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 448) := by decide
/-- ` 268: 00550e33  add x28,x10,x5` -/
theorem dec_268 : Rv64i.decode (wordAt1 268) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 272: 000e4383  lbu x7,0(x28)` -/
theorem dec_272 : Rv64i.decode (wordAt1 272) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 276: 00128293  addi x5,x5,1` -/
theorem dec_276 : Rv64i.decode (wordAt1 276) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 280: 00339e13  slli x28,x7,0x3` -/
theorem dec_280 : Rv64i.decode (wordAt1 280) = Rv64i.Instr.slli 28 7 3 := by decide
/-- ` 284: 00ee0e33  add x28,x28,x14` -/
theorem dec_284 : Rv64i.decode (wordAt1 284) = Rv64i.Instr.add 28 28 14 := by decide
/-- ` 288: 000e3e83  ld x29,0(x28)` -/
theorem dec_288 : Rv64i.decode (wordAt1 288) = Rv64i.Instr.ld 29 28 (BitVec.ofNat 12 0) := by decide
/-- ` 292: 180ed663  bge x29,x0,80000340 <core1+0x2b0>` -/
theorem dec_292 : Rv64i.decode (wordAt1 292) = Rv64i.Instr.bge 29 0 (BitVec.ofNat 13 396) := by decide
/-- ` 296: 006e3023  sd x6,0(x28)` -/
theorem dec_296 : Rv64i.decode (wordAt1 296) = Rv64i.Instr.sd 28 6 (BitVec.ofNat 12 0) := by decide
/-- ` 300: ef9ff06f  jal x0,800000b4 <core1+0x24>` -/
theorem dec_300 : Rv64i.decode (wordAt1 300) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2096888) := by decide
/-- ` 304: 18b2fc63  bgeu x5,x11,80000358 <core1+0x2c8>` -/
theorem dec_304 : Rv64i.decode (wordAt1 304) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 408) := by decide
/-- ` 308: 00128293  addi x5,x5,1` -/
theorem dec_308 : Rv64i.decode (wordAt1 308) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 312: 40668e33  sub x28,x13,x6` -/
theorem dec_312 : Rv64i.decode (wordAt1 312) = Rv64i.Instr.sub 28 13 6 := by decide
/-- ` 316: 00400e93  addi x29,x0,4` -/
theorem dec_316 : Rv64i.decode (wordAt1 316) = Rv64i.Instr.addi 29 0 (BitVec.ofNat 12 4) := by decide
/-- ` 320: 15de4063  blt x28,x29,80000310 <core1+0x280>` -/
theorem dec_320 : Rv64i.decode (wordAt1 320) = Rv64i.Instr.blt 28 29 (BitVec.ofNat 13 320) := by decide
/-- ` 324: 00430313  addi x6,x6,4` -/
theorem dec_324 : Rv64i.decode (wordAt1 324) = Rv64i.Instr.addi 6 6 (BitVec.ofNat 12 4) := by decide
/-- ` 328: eddff06f  jal x0,800000b4 <core1+0x24>` -/
theorem dec_328 : Rv64i.decode (wordAt1 328) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2096860) := by decide
/-- ` 332: 00b2fe63  bgeu x5,x11,800001f8 <core1+0x168>` -/
theorem dec_332 : Rv64i.decode (wordAt1 332) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 28) := by decide
/-- ` 336: 00550e33  add x28,x10,x5` -/
theorem dec_336 : Rv64i.decode (wordAt1 336) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 340: 000e4383  lbu x7,0(x28)` -/
theorem dec_340 : Rv64i.decode (wordAt1 340) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 344: 00a00e13  addi x28,x0,10` -/
theorem dec_344 : Rv64i.decode (wordAt1 344) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 10) := by decide
/-- ` 348: edc384e3  beq x7,x28,800000b4 <core1+0x24>` -/
theorem dec_348 : Rv64i.decode (wordAt1 348) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 7880) := by decide
/-- ` 352: 00128293  addi x5,x5,1` -/
theorem dec_352 : Rv64i.decode (wordAt1 352) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 356: fe9ff06f  jal x0,800001dc <core1+0x14c>` -/
theorem dec_356 : Rv64i.decode (wordAt1 356) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2097128) := by decide
/-- ` 360: 00000293  addi x5,x0,0` -/
theorem dec_360 : Rv64i.decode (wordAt1 360) = Rv64i.Instr.addi 5 0 (BitVec.ofNat 12 0) := by decide
/-- ` 364: 00000313  addi x6,x0,0` -/
theorem dec_364 : Rv64i.decode (wordAt1 364) = Rv64i.Instr.addi 6 0 (BitVec.ofNat 12 0) := by decide
/-- ` 368: 10b2f263  bgeu x5,x11,80000304 <core1+0x274>` -/
theorem dec_368 : Rv64i.decode (wordAt1 368) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 260) := by decide
/-- ` 372: 00550e33  add x28,x10,x5` -/
theorem dec_372 : Rv64i.decode (wordAt1 372) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 376: 000e4383  lbu x7,0(x28)` -/
theorem dec_376 : Rv64i.decode (wordAt1 376) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 380: 00128293  addi x5,x5,1` -/
theorem dec_380 : Rv64i.decode (wordAt1 380) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 384: 02300e13  addi x28,x0,35` -/
theorem dec_384 : Rv64i.decode (wordAt1 384) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 35) := by decide
/-- ` 388: 0dc38a63  beq x7,x28,800002e8 <core1+0x258>` -/
theorem dec_388 : Rv64i.decode (wordAt1 388) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 212) := by decide
/-- ` 392: 03b00e13  addi x28,x0,59` -/
theorem dec_392 : Rv64i.decode (wordAt1 392) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 59) := by decide
/-- ` 396: 0dc38663  beq x7,x28,800002e8 <core1+0x258>` -/
theorem dec_396 : Rv64i.decode (wordAt1 396) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 204) := by decide
/-- ` 400: 00a00e13  addi x28,x0,10` -/
theorem dec_400 : Rv64i.decode (wordAt1 400) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 10) := by decide
/-- ` 404: fdc38ee3  beq x7,x28,80000200 <core1+0x170>` -/
theorem dec_404 : Rv64i.decode (wordAt1 404) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 8156) := by decide
/-- ` 408: 02000e13  addi x28,x0,32` -/
theorem dec_408 : Rv64i.decode (wordAt1 408) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 32) := by decide
/-- ` 412: fdc38ae3  beq x7,x28,80000200 <core1+0x170>` -/
theorem dec_412 : Rv64i.decode (wordAt1 412) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 8148) := by decide
/-- ` 416: 05f00e13  addi x28,x0,95` -/
theorem dec_416 : Rv64i.decode (wordAt1 416) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 95) := by decide
/-- ` 420: fdc386e3  beq x7,x28,80000200 <core1+0x170>` -/
theorem dec_420 : Rv64i.decode (wordAt1 420) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 8140) := by decide
/-- ` 424: 03a00e13  addi x28,x0,58` -/
theorem dec_424 : Rv64i.decode (wordAt1 424) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- ` 428: 05c38c63  beq x7,x28,80000294 <core1+0x204>` -/
theorem dec_428 : Rv64i.decode (wordAt1 428) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 88) := by decide
/-- ` 432: 02500e13  addi x28,x0,37` -/
theorem dec_432 : Rv64i.decode (wordAt1 432) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 37) := by decide
/-- ` 436: 05c38c63  beq x7,x28,8000029c <core1+0x20c>` -/
theorem dec_436 : Rv64i.decode (wordAt1 436) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 88) := by decide
/-- ` 440: 03a00e13  addi x28,x0,58` -/
theorem dec_440 : Rv64i.decode (wordAt1 440) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- ` 444: 01c3c663  blt x7,x28,80000258 <core1+0x1c8>` -/
theorem dec_444 : Rv64i.decode (wordAt1 444) = Rv64i.Instr.blt 7 28 (BitVec.ofNat 13 12) := by decide
/-- ` 448: fc938e93  addi x29,x7,-55` -/
theorem dec_448 : Rv64i.decode (wordAt1 448) = Rv64i.Instr.addi 29 7 (BitVec.ofNat 12 4041) := by decide
/-- ` 452: 0080006f  jal x0,8000025c <core1+0x1cc>` -/
theorem dec_452 : Rv64i.decode (wordAt1 452) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 8) := by decide
/-- ` 456: fd038e93  addi x29,x7,-48` -/
theorem dec_456 : Rv64i.decode (wordAt1 456) = Rv64i.Instr.addi 29 7 (BitVec.ofNat 12 4048) := by decide
/-- ` 460: 00550e33  add x28,x10,x5` -/
theorem dec_460 : Rv64i.decode (wordAt1 460) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 464: 000e4383  lbu x7,0(x28)` -/
theorem dec_464 : Rv64i.decode (wordAt1 464) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 468: 00128293  addi x5,x5,1` -/
theorem dec_468 : Rv64i.decode (wordAt1 468) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 472: 03a00e13  addi x28,x0,58` -/
theorem dec_472 : Rv64i.decode (wordAt1 472) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 58) := by decide
/-- ` 476: 01c3c663  blt x7,x28,80000278 <core1+0x1e8>` -/
theorem dec_476 : Rv64i.decode (wordAt1 476) = Rv64i.Instr.blt 7 28 (BitVec.ofNat 13 12) := by decide
/-- ` 480: fc938f13  addi x30,x7,-55` -/
theorem dec_480 : Rv64i.decode (wordAt1 480) = Rv64i.Instr.addi 30 7 (BitVec.ofNat 12 4041) := by decide
/-- ` 484: 0080006f  jal x0,8000027c <core1+0x1ec>` -/
theorem dec_484 : Rv64i.decode (wordAt1 484) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 8) := by decide
/-- ` 488: fd038f13  addi x30,x7,-48` -/
theorem dec_488 : Rv64i.decode (wordAt1 488) = Rv64i.Instr.addi 30 7 (BitVec.ofNat 12 4048) := by decide
/-- ` 492: 004e9e93  slli x29,x29,0x4` -/
theorem dec_492 : Rv64i.decode (wordAt1 492) = Rv64i.Instr.slli 29 29 4 := by decide
/-- ` 496: 01eeeeb3  or x29,x29,x30` -/
theorem dec_496 : Rv64i.decode (wordAt1 496) = Rv64i.Instr.or 29 29 30 := by decide
/-- ` 500: 00660e33  add x28,x12,x6` -/
theorem dec_500 : Rv64i.decode (wordAt1 500) = Rv64i.Instr.add 28 12 6 := by decide
/-- ` 504: 01de0023  sb x29,0(x28)` -/
theorem dec_504 : Rv64i.decode (wordAt1 504) = Rv64i.Instr.sb 28 29 (BitVec.ofNat 12 0) := by decide
/-- ` 508: 00130313  addi x6,x6,1` -/
theorem dec_508 : Rv64i.decode (wordAt1 508) = Rv64i.Instr.addi 6 6 (BitVec.ofNat 12 1) := by decide
/-- ` 512: f71ff06f  jal x0,80000200 <core1+0x170>` -/
theorem dec_512 : Rv64i.decode (wordAt1 512) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2097008) := by decide
/-- ` 516: 00128293  addi x5,x5,1` -/
theorem dec_516 : Rv64i.decode (wordAt1 516) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 520: f69ff06f  jal x0,80000200 <core1+0x170>` -/
theorem dec_520 : Rv64i.decode (wordAt1 520) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2097000) := by decide
/-- ` 524: 00550e33  add x28,x10,x5` -/
theorem dec_524 : Rv64i.decode (wordAt1 524) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 528: 000e4383  lbu x7,0(x28)` -/
theorem dec_528 : Rv64i.decode (wordAt1 528) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 532: 00128293  addi x5,x5,1` -/
theorem dec_532 : Rv64i.decode (wordAt1 532) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 536: 00339e13  slli x28,x7,0x3` -/
theorem dec_536 : Rv64i.decode (wordAt1 536) = Rv64i.Instr.slli 28 7 3 := by decide
/-- ` 540: 00ee0e33  add x28,x28,x14` -/
theorem dec_540 : Rv64i.decode (wordAt1 540) = Rv64i.Instr.add 28 28 14 := by decide
/-- ` 544: 000e3e83  ld x29,0(x28)` -/
theorem dec_544 : Rv64i.decode (wordAt1 544) = Rv64i.Instr.ld 29 28 (BitVec.ofNat 12 0) := by decide
/-- ` 548: 080ecc63  blt x29,x0,8000034c <core1+0x2bc>` -/
theorem dec_548 : Rv64i.decode (wordAt1 548) = Rv64i.Instr.blt 29 0 (BitVec.ofNat 13 152) := by decide
/-- ` 552: 00430f13  addi x30,x6,4` -/
theorem dec_552 : Rv64i.decode (wordAt1 552) = Rv64i.Instr.addi 30 6 (BitVec.ofNat 12 4) := by decide
/-- ` 556: 41ee8eb3  sub x29,x29,x30` -/
theorem dec_556 : Rv64i.decode (wordAt1 556) = Rv64i.Instr.sub 29 29 30 := by decide
/-- ` 560: 00660e33  add x28,x12,x6` -/
theorem dec_560 : Rv64i.decode (wordAt1 560) = Rv64i.Instr.add 28 12 6 := by decide
/-- ` 564: 01de0023  sb x29,0(x28)` -/
theorem dec_564 : Rv64i.decode (wordAt1 564) = Rv64i.Instr.sb 28 29 (BitVec.ofNat 12 0) := by decide
/-- ` 568: 008ede93  srli x29,x29,0x8` -/
theorem dec_568 : Rv64i.decode (wordAt1 568) = Rv64i.Instr.srli 29 29 8 := by decide
/-- ` 572: 01de00a3  sb x29,1(x28)` -/
theorem dec_572 : Rv64i.decode (wordAt1 572) = Rv64i.Instr.sb 28 29 (BitVec.ofNat 12 1) := by decide
/-- ` 576: 008ede93  srli x29,x29,0x8` -/
theorem dec_576 : Rv64i.decode (wordAt1 576) = Rv64i.Instr.srli 29 29 8 := by decide
/-- ` 580: 01de0123  sb x29,2(x28)` -/
theorem dec_580 : Rv64i.decode (wordAt1 580) = Rv64i.Instr.sb 28 29 (BitVec.ofNat 12 2) := by decide
/-- ` 584: 008ede93  srli x29,x29,0x8` -/
theorem dec_584 : Rv64i.decode (wordAt1 584) = Rv64i.Instr.srli 29 29 8 := by decide
/-- ` 588: 01de01a3  sb x29,3(x28)` -/
theorem dec_588 : Rv64i.decode (wordAt1 588) = Rv64i.Instr.sb 28 29 (BitVec.ofNat 12 3) := by decide
/-- ` 592: 00430313  addi x6,x6,4` -/
theorem dec_592 : Rv64i.decode (wordAt1 592) = Rv64i.Instr.addi 6 6 (BitVec.ofNat 12 4) := by decide
/-- ` 596: f1dff06f  jal x0,80000200 <core1+0x170>` -/
theorem dec_596 : Rv64i.decode (wordAt1 596) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2096924) := by decide
/-- ` 600: 00b2fe63  bgeu x5,x11,80000304 <core1+0x274>` -/
theorem dec_600 : Rv64i.decode (wordAt1 600) = Rv64i.Instr.bgeu 5 11 (BitVec.ofNat 13 28) := by decide
/-- ` 604: 00550e33  add x28,x10,x5` -/
theorem dec_604 : Rv64i.decode (wordAt1 604) = Rv64i.Instr.add 28 10 5 := by decide
/-- ` 608: 000e4383  lbu x7,0(x28)` -/
theorem dec_608 : Rv64i.decode (wordAt1 608) = Rv64i.Instr.lbu 7 28 (BitVec.ofNat 12 0) := by decide
/-- ` 612: 00a00e13  addi x28,x0,10` -/
theorem dec_612 : Rv64i.decode (wordAt1 612) = Rv64i.Instr.addi 28 0 (BitVec.ofNat 12 10) := by decide
/-- ` 616: f1c384e3  beq x7,x28,80000200 <core1+0x170>` -/
theorem dec_616 : Rv64i.decode (wordAt1 616) = Rv64i.Instr.beq 7 28 (BitVec.ofNat 13 7944) := by decide
/-- ` 620: 00128293  addi x5,x5,1` -/
theorem dec_620 : Rv64i.decode (wordAt1 620) = Rv64i.Instr.addi 5 5 (BitVec.ofNat 12 1) := by decide
/-- ` 624: fe9ff06f  jal x0,800002e8 <core1+0x258>` -/
theorem dec_624 : Rv64i.decode (wordAt1 624) = Rv64i.Instr.jal 0 (BitVec.ofNat 21 2097128) := by decide
/-- ` 628: 00000513  addi x10,x0,0` -/
theorem dec_628 : Rv64i.decode (wordAt1 628) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 0) := by decide
/-- ` 632: 00030593  addi x11,x6,0` -/
theorem dec_632 : Rv64i.decode (wordAt1 632) = Rv64i.Instr.addi 11 6 (BitVec.ofNat 12 0) := by decide
/-- ` 636: 00008067  jalr x0,0(x1)` -/
theorem dec_636 : Rv64i.decode (wordAt1 636) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 640: 00200513  addi x10,x0,2` -/
theorem dec_640 : Rv64i.decode (wordAt1 640) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 2) := by decide
/-- ` 644: 00000593  addi x11,x0,0` -/
theorem dec_644 : Rv64i.decode (wordAt1 644) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0) := by decide
/-- ` 648: 00008067  jalr x0,0(x1)` -/
theorem dec_648 : Rv64i.decode (wordAt1 648) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 652: 00300513  addi x10,x0,3` -/
theorem dec_652 : Rv64i.decode (wordAt1 652) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 3) := by decide
/-- ` 656: 00000593  addi x11,x0,0` -/
theorem dec_656 : Rv64i.decode (wordAt1 656) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0) := by decide
/-- ` 660: 00008067  jalr x0,0(x1)` -/
theorem dec_660 : Rv64i.decode (wordAt1 660) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 664: 00400513  addi x10,x0,4` -/
theorem dec_664 : Rv64i.decode (wordAt1 664) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 4) := by decide
/-- ` 668: 00000593  addi x11,x0,0` -/
theorem dec_668 : Rv64i.decode (wordAt1 668) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0) := by decide
/-- ` 672: 00008067  jalr x0,0(x1)` -/
theorem dec_672 : Rv64i.decode (wordAt1 672) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 676: 00500513  addi x10,x0,5` -/
theorem dec_676 : Rv64i.decode (wordAt1 676) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 5) := by decide
/-- ` 680: 00000593  addi x11,x0,0` -/
theorem dec_680 : Rv64i.decode (wordAt1 680) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0) := by decide
/-- ` 684: 00008067  jalr x0,0(x1)` -/
theorem dec_684 : Rv64i.decode (wordAt1 684) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 688: 00600513  addi x10,x0,6` -/
theorem dec_688 : Rv64i.decode (wordAt1 688) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 6) := by decide
/-- ` 692: 00000593  addi x11,x0,0` -/
theorem dec_692 : Rv64i.decode (wordAt1 692) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0) := by decide
/-- ` 696: 00008067  jalr x0,0(x1)` -/
theorem dec_696 : Rv64i.decode (wordAt1 696) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 700: 00700513  addi x10,x0,7` -/
theorem dec_700 : Rv64i.decode (wordAt1 700) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 7) := by decide
/-- ` 704: 00030593  addi x11,x6,0` -/
theorem dec_704 : Rv64i.decode (wordAt1 704) = Rv64i.Instr.addi 11 6 (BitVec.ofNat 12 0) := by decide
/-- ` 708: 00008067  jalr x0,0(x1)` -/
theorem dec_708 : Rv64i.decode (wordAt1 708) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide
/-- ` 712: 00800513  addi x10,x0,8` -/
theorem dec_712 : Rv64i.decode (wordAt1 712) = Rv64i.Instr.addi 10 0 (BitVec.ofNat 12 8) := by decide
/-- ` 716: 00000593  addi x11,x0,0` -/
theorem dec_716 : Rv64i.decode (wordAt1 716) = Rv64i.Instr.addi 11 0 (BitVec.ofNat 12 0) := by decide
/-- ` 720: 00008067  jalr x0,0(x1)` -/
theorem dec_720 : Rv64i.decode (wordAt1 720) = Rv64i.Instr.jalr 0 1 (BitVec.ofNat 12 0) := by decide

end Hex1.Refine
