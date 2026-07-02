/-
  LowIR.ProgSim.MemFacts — the `StInv` algebra for the IL memory ops
  (RESUME-PROGSIM Phase 4.2). Where SlotFacts handled the compiler's PRIVATE frame
  slots (`storeWord` at `sp + slotOff r`, mirroring `rset`), this file handles the
  USER memory ops (`ld`/`sd`/`lbu`/`sb`): the IL and the machine touch the SAME
  address (the P1 payoff — `x2 ≡ sp`, so the slot-loaded base + imm equals the IL
  address literally), and correctness needs only that the touched bytes lie off the
  machine-private region (the frame hole + code blob).

  Two ingredients:
    * agreement — `St.loadWord`/`State.loadWord` are byte-identical, so equal base
      bytes give equal loads (`loadWord_agree`); a `storeWord`/`storeByte` writes
      identical bytes into IL and machine memory, so it preserves agreement pointwise
      (`storeWord_mem_agree` — the key: no in-range/out-range split, since the stored
      bytes are literally the same expression on both sides);
    * preservation — a user `storeWord`/`storeByte` whose range is off THIS
      activation's hole (⇒ disjoint from every live slot) and off the blob
      (⇒ `Installed` survives) preserves `StInv`, with `s.storeWord addr v` on the
      IL side (`StInv_storeWord_user`/`StInv_storeByte_user`).

  Register binders are `Nat` (a `≤` at `Reg = abbrev Nat` hides from `omega`).
  `@[inline]` note: `St.storeByte`/`St.loadByte` don't unfold via `simp [name]`; use
  the FULL name with `unfold` (the opened alias fails too). Kept `[propext, Quot.sound]`.
-/
import LowIR.ProgSim.SlotFacts

namespace LowIR.ProgSim

open LowIR.Prog (Name FunDef St)
open LowIR.Compile (userOff slotOff maxRegF)
open Rv64i (Word Byte State)

/-! ## §1 — load/store byte agreement (IL ↔ machine, same base bytes). -/

/-- `St.loadWord` and `State.loadWord` are the same little-endian read, so if the
    eight base bytes `a … a+7` agree, the 64-bit loads agree. -/
theorem loadWord_agree (s : St) (m : State) (a : Word)
    (h0 : s.mem a = m.mem a) (h1 : s.mem (a + 1) = m.mem (a + 1))
    (h2 : s.mem (a + 2) = m.mem (a + 2)) (h3 : s.mem (a + 3) = m.mem (a + 3))
    (h4 : s.mem (a + 4) = m.mem (a + 4)) (h5 : s.mem (a + 5) = m.mem (a + 5))
    (h6 : s.mem (a + 6) = m.mem (a + 6)) (h7 : s.mem (a + 7) = m.mem (a + 7)) :
    s.loadWord a = m.loadWord a := by
  simp only [St.loadWord, State.loadWord, h0, h1, h2, h3, h4, h5, h6, h7]

/-- Single-byte agreement (both are `.mem a` definitionally). -/
theorem loadByte_agree (s : St) (m : State) (a : Word) (h : s.mem a = m.mem a) :
    s.loadByte a = m.loadByte a := h

/-- A `storeWord` writes identical bytes into IL and machine memory, so wherever the
    base bytes agree, the results agree — no in-range/out-of-range split needed. -/
theorem storeWord_mem_agree (s : St) (m : State) (addr v a : Word)
    (h : s.mem a = m.mem a) :
    (s.storeWord addr v).mem a = (m.storeWord addr v).mem a := by
  unfold LowIR.Prog.St.storeWord LowIR.Prog.St.storeByte
  simp only [State.storeWord, State.storeByte, h]

theorem storeByte_mem_agree (s : St) (m : State) (addr : Word) (b : Byte) (a : Word)
    (h : s.mem a = m.mem a) :
    (s.storeByte addr b).mem a = (m.storeByte addr b).mem a := by
  unfold LowIR.Prog.St.storeByte
  simp only [State.storeByte, h]

/-! ## §2 — register / sp are untouched by a memory store. -/

theorem St_storeWord_sp (s : St) (addr v : Word) : (s.storeWord addr v).sp = s.sp := by
  unfold LowIR.Prog.St.storeWord LowIR.Prog.St.storeByte; rfl

theorem St_storeWord_rget (s : St) (addr v : Word) (r : Nat) :
    (s.storeWord addr v).rget r = s.rget r := by
  unfold LowIR.Prog.St.storeWord LowIR.Prog.St.storeByte LowIR.Prog.St.rget; rfl

theorem St_storeByte_sp (s : St) (addr : Word) (b : Byte) : (s.storeByte addr b).sp = s.sp := by
  unfold LowIR.Prog.St.storeByte; rfl

theorem St_storeByte_rget (s : St) (addr : Word) (b : Byte) (r : Nat) :
    (s.storeByte addr b).rget r = s.rget r := by
  unfold LowIR.Prog.St.storeByte LowIR.Prog.St.rget; rfl

theorem State_storeWord_rget (m : State) (addr v : Word) (r : Nat) :
    (m.storeWord addr v).rget r = m.rget r := by
  simp [State.storeWord, State.storeByte, State.rget]

theorem State_storeByte_rget (m : State) (addr : Word) (b : Byte) (r : Nat) :
    (m.storeByte addr b).rget r = m.rget r := by
  simp [State.storeByte, State.rget]

/-! ## §3 — the payoff: a user `storeWord` preserves `StInv`.

    The store hits `addr`, off THIS activation's hole `[sp, sp + userOff fd)` (so
    disjoint from every live slot, which sits inside the hole) and off the blob (so
    `Installed` survives). Both sides store the same `v`, so off-`MachPriv` agreement
    is preserved pointwise. `x2 ≡ sp`, the hole record, and alignment are untouched
    (the store hits memory, not registers or `sp`). -/
theorem StInv_storeWord_user (L : Layout) (fd : FunDef) (holes : List Hole)
    (s : St) (m : State) (addr v : Word)
    (hinv : StInv L fd holes s m)
    (hwa : addr.toNat + 8 ≤ 2 ^ 64)
    (hhole : addr.toNat + 8 ≤ s.sp.toNat ∨ s.sp.toNat + userOff fd ≤ addr.toNat)
    (hbd : L.codeBase.toNat + L.blobLen ≤ addr.toNat ∨ addr.toNat + 8 ≤ L.codeBase.toNat)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hnw : s.sp.toNat + userOff fd ≤ 2 ^ 64) :
    StInv L fd holes (s.storeWord addr v) (m.storeWord addr v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
  have hsp' : (s.storeWord addr v).sp = s.sp := St_storeWord_sp s addr v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp', State_storeWord_rget m addr v 2]; exact h1
  · intro r hr1 hrm
    rw [hsp', St_storeWord_rget s addr v r]
    have hslot : slotOff r + 8 ≤ userOff fd := slotOff_add8_le_userOff fd r hrm
    have hst : (s.sp + BitVec.ofNat 64 (slotOff r)).toNat = s.sp.toNat + slotOff r :=
      slotAddr_toNat s.sp r (by omega)
    rw [Rv64i.loadWord_storeWord_disjoint m addr (s.sp + BitVec.ofNat 64 (slotOff r)) v hwa
          (by rw [hst]; omega) (by
            rw [hst]; rcases hhole with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))]
    exact h2 r hr1 hrm
  · exact Installed_storeWord_off_blob L m addr v h3 hseg hblob hwa hbd
  · intro a hna; exact storeWord_mem_agree s m addr v a (h4 a hna)
  · rw [hsp']; exact h5
  · rw [hsp']; exact h6

/-! ## §4 — a user `storeByte` preserves `StInv`. Same shape; one byte, so the
    slot/blob disjointness only needs `addr` (not `addr..addr+7`) off the ranges. -/

/-- A single-byte store leaves every 8-byte `loadWord` at a disjoint base untouched. -/
theorem loadWord_storeByte_ne (m : State) (addr : Word) (b : Byte) (a' : Word)
    (hwa' : a'.toNat + 8 ≤ 2 ^ 64)
    (hd : addr.toNat + 1 ≤ a'.toNat ∨ a'.toNat + 8 ≤ addr.toNat) :
    (m.storeByte addr b).loadWord a' = m.loadWord a' := by
  simp only [State.loadWord, State.storeByte]
  have key : ∀ y : Word, y.toNat < a'.toNat + 8 → a'.toNat ≤ y.toNat →
      (if y = addr then b else m.mem y) = m.mem y := by
    intro y hlt hge
    rw [if_neg]
    intro heq
    have := congrArg BitVec.toNat heq
    omega
  rw [key a' (by omega) (by omega), key (a'+1) ?_ ?_, key (a'+2) ?_ ?_, key (a'+3) ?_ ?_,
      key (a'+4) ?_ ?_, key (a'+5) ?_ ?_, key (a'+6) ?_ ?_, key (a'+7) ?_ ?_]
  all_goals (simp only [BitVec.toNat_add, BitVec.reduceToNat, Nat.reducePow]; omega)

/-- A `storeByte` whose address is off the blob preserves every blob byte. -/
theorem mem_storeByte_off_blob (L : Layout) (m : State) (addr : Word) (b : Byte) (K : Nat)
    (hK : K < L.blobLen) (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hdisj : L.codeBase.toNat + L.blobLen ≤ addr.toNat ∨ addr.toNat + 1 ≤ L.codeBase.toNat) :
    (m.storeByte addr b).mem (L.codeBase + BitVec.ofNat 64 K)
      = m.mem (L.codeBase + BitVec.ofNat 64 K) := by
  have hy := blobAddr_toNat L K hK hblob
  simp only [State.storeByte]
  rw [if_neg]
  intro heq; rw [heq] at hy; omega

/-- `Installed` survives a `storeByte` off the blob (byte analogue of the
    `storeWord` lemma; the four fetch bytes and every data byte are all missed). -/
theorem Installed_storeByte_off_blob (L : Layout) (m : State) (addr : Word) (b : Byte)
    (hinst : Installed L m) (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hdisj : L.codeBase.toNat + L.blobLen ≤ addr.toNat ∨ addr.toNat + 1 ≤ L.codeBase.toNat) :
    Installed L (m.storeByte addr b) := by
  obtain ⟨hcode, hdata⟩ := hinst
  have hbl : L.segStart ≤ L.blobLen := by simp only [Layout.blobLen]; omega
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · have e0 := mem_storeByte_off_blob L m addr b (4 * j) (by omega) hblob hdisj
    have key : ∀ c : Nat, c < 4 →
        (m.storeByte addr b).mem (L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c)
          = m.mem (L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c) := by
      intro c hc
      have : L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c
               = L.codeBase + BitVec.ofNat 64 (4 * j + c) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [this]; exact mem_storeByte_off_blob L m addr b (4 * j + c) (by omega) hblob hdisj
    rw [← hcode j hj]
    exact congrArg Rv64i.decode
      (fetch32_pc_congr _ _ _ e0 (key 1 (by omega)) (key 2 (by omega)) (key 3 (by omega)))
  · have : L.segStart + i < L.blobLen := by simp only [Layout.blobLen]; omega
    rw [mem_storeByte_off_blob L m addr b (L.segStart + i) this hblob hdisj]
    exact hdata i hi

theorem StInv_storeByte_user (L : Layout) (fd : FunDef) (holes : List Hole)
    (s : St) (m : State) (addr : Word) (b : Byte)
    (hinv : StInv L fd holes s m)
    (hhole : addr.toNat + 1 ≤ s.sp.toNat ∨ s.sp.toNat + userOff fd ≤ addr.toNat)
    (hbd : L.codeBase.toNat + L.blobLen ≤ addr.toNat ∨ addr.toNat + 1 ≤ L.codeBase.toNat)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hnw : s.sp.toNat + userOff fd ≤ 2 ^ 64) :
    StInv L fd holes (s.storeByte addr b) (m.storeByte addr b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
  have hsp' : (s.storeByte addr b).sp = s.sp := St_storeByte_sp s addr b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp', State_storeByte_rget m addr b 2]; exact h1
  · intro r hr1 hrm
    rw [hsp', St_storeByte_rget s addr b r]
    have hslot : slotOff r + 8 ≤ userOff fd := slotOff_add8_le_userOff fd r hrm
    have hst : (s.sp + BitVec.ofNat 64 (slotOff r)).toNat = s.sp.toNat + slotOff r :=
      slotAddr_toNat s.sp r (by omega)
    rw [loadWord_storeByte_ne m addr b (s.sp + BitVec.ofNat 64 (slotOff r))
          (by rw [hst]; omega) (by
            rw [hst]; rcases hhole with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))]
    exact h2 r hr1 hrm
  · exact Installed_storeByte_off_blob L m addr b h3 hseg hblob hbd
  · intro a hna; exact storeByte_mem_agree s m addr b a (h4 a hna)
  · rw [hsp']; exact h5
  · rw [hsp']; exact h6

end LowIR.ProgSim
