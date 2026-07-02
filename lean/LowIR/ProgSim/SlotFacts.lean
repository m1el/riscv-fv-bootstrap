/-
  LowIR.ProgSim.SlotFacts — the `StInv` slot algebra (RESUME-PROGSIM Phase 3
  finish). WordMem gave the raw 64-bit LE load/store round-trip and disjointness;
  this file lifts those to the compiler's frame layout (`slotOff r = 8*(1+r)`,
  the user-visible register slots sit in `[sp, sp + userOff fd)`) and then bundles
  the payoff: a machine `storeWord` into IL register `r`'s slot mirrors the IL
  `rset r v`, preserving `StInv`.

  The three ingredients, each a standalone reusable lemma:
    * slot arithmetic — `slotOff r + 8 ≤ userOff fd` for `r ≤ maxRegF fd`, and the
      no-wrap `toNat` of a slot address (needed to feed WordMem's `toNat` side
      conditions);
    * slot read/write — store to slot `r` reads back `v` (`loadWord_store_slot_same`)
      and leaves every OTHER slot untouched (`loadWord_store_slot_ne`, via 8-byte
      disjointness);
    * blob/off-priv preservation — a slot store lands in the frame hole, disjoint
      from the code+data blob, so `Installed` and off-`MachPriv` memory survive.

  Then `StInv_store_slot`: the whole invariant is preserved by the slot store,
  with `s.rset r v` on the IL side. The blob⊥hole disjointness is taken as an
  explicit hypothesis here (Phase 4/5 discharge it from `SimPre`).
-/
import LowIR.ProgSim.Defs

namespace LowIR.ProgSim

open LowIR.Prog (Name FunDef Data pad8 dataSegment)
open LowIR.Compile (userOff totalFrame slotOff maxRegF)
open Rv64i (Word Byte State fetch32 decode)

-- `LowIR.Reg` is `abbrev Nat`, but stating a `≤`/`≠` hypothesis at type `Reg`
-- hides it from `omega` (it matches `LE.le`/`≠` only at literal `Nat`). So every
-- register binder in this file is `Nat`; `slotOff`/`maxRegF` accept it by defeq.

/-! ## §1 — slot-offset arithmetic (Nat level). -/

/-- A live register's 8-byte slot fits inside the user-frame hole:
    `slotOff r = 8*(1+r)` and `userOff fd = 8*(maxRegF fd + 2)`, so
    `slotOff r + 8 = 8*(2+r) ≤ 8*(2 + maxRegF fd) = userOff fd`. -/
theorem slotOff_add8_le_userOff (fd : FunDef) (r : Nat) (h : r ≤ maxRegF fd) :
    slotOff r + 8 ≤ userOff fd := by
  unfold slotOff userOff; omega

/-- Distinct registers have 8-apart slots: `slotOff` is injective with gap ≥ 8. -/
theorem slotOff_disjoint (r r' : Nat) (h : r ≠ r') :
    slotOff r + 8 ≤ slotOff r' ∨ slotOff r' + 8 ≤ slotOff r := by
  unfold slotOff; omega

/-! ## §2 — slot-address `toNat` (no-wrap). -/

/-- The slot address `sp + slotOff r` does not wrap: its `toNat` is the plain
    sum. Provided the frame `[sp, sp + userOff fd)` lives below `2⁶⁴` and `r` is
    a live register (so `slotOff r < userOff fd`). -/
theorem slotAddr_toNat (sp : Word) (r : Nat)
    (hlt : sp.toNat + slotOff r < 2 ^ 64) :
    (sp + BitVec.ofNat 64 (slotOff r)).toNat = sp.toNat + slotOff r := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-! ## §3 — slot read/write (WordMem lifted to slot addresses). -/

/-- Store to slot `r`, read slot `r` back: the round-trip (WordMem's
    `loadWord_storeWord_same` at the slot address — no side condition, the eight
    byte offsets are distinct literals). -/
theorem loadWord_store_slot_same (m : State) (sp v : Word) (r : Nat) :
    (m.storeWord (sp + BitVec.ofNat 64 (slotOff r)) v).loadWord
      (sp + BitVec.ofNat 64 (slotOff r)) = v :=
  Rv64i.loadWord_storeWord_same m _ v

/-- Store to slot `r` leaves slot `r' ≠ r` untouched: the two 8-byte slots are
    disjoint (`slotOff_disjoint`), so WordMem's `loadWord_storeWord_disjoint`
    applies. Both slot addresses must be wrap-free (frame below `2⁶⁴`). -/
theorem loadWord_store_slot_ne (m : State) (sp v : Word) (r r' : Nat)
    (hr : r ≠ r')
    (hb  : sp.toNat + slotOff r  + 8 ≤ 2 ^ 64)
    (hb' : sp.toNat + slotOff r' + 8 ≤ 2 ^ 64) :
    (m.storeWord (sp + BitVec.ofNat 64 (slotOff r)) v).loadWord
        (sp + BitVec.ofNat 64 (slotOff r'))
      = m.loadWord (sp + BitVec.ofNat 64 (slotOff r')) := by
  apply Rv64i.loadWord_storeWord_disjoint
  · rw [slotAddr_toNat sp r (by omega)]; omega
  · rw [slotAddr_toNat sp r' (by omega)]; omega
  · rw [slotAddr_toNat sp r (by omega), slotAddr_toNat sp r' (by omega)]
    rcases slotOff_disjoint r r' hr with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-! ## §4 — blob preservation: a store off the code+data blob keeps `Installed`.

    A slot store lands in the frame hole; when that hole is disjoint from the
    blob (the compiler places code+data far from the stack — supplied by `SimPre`
    downstream), the 8 stored bytes miss every code/data byte, so the trusted
    machine still fetches the same instructions and reads the same const data. -/

/-- `fetch32` depends only on the four bytes at `pc … pc+3`: if two states agree
    there (and share the overridden `pc`), they fetch the same word. -/
theorem fetch32_pc_congr (m1 m2 : State) (P : Word)
    (h0 : m1.mem P = m2.mem P) (h1 : m1.mem (P + 1) = m2.mem (P + 1))
    (h2 : m1.mem (P + 2) = m2.mem (P + 2)) (h3 : m1.mem (P + 3) = m2.mem (P + 3)) :
    fetch32 { m1 with pc := P } = fetch32 { m2 with pc := P } := by
  simp only [fetch32, h0, h1, h2, h3]

/-- The `toNat` of a blob byte address `codeBase + K` (`K < blobLen`, blob
    wrap-free) is the plain sum — used to place every code/data read inside the
    disjoint-from-store window. -/
theorem blobAddr_toNat (L : Layout) (K : Nat) (hK : K < L.blobLen)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64) :
    (L.codeBase + BitVec.ofNat 64 K).toNat = L.codeBase.toNat + K := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- A store whose 8-byte range `[a, a+8)` is disjoint from the blob preserves
    every blob byte `codeBase + K` (`K < blobLen`). -/
theorem mem_storeWord_off_blob (L : Layout) (m : State) (a v : Word) (K : Nat)
    (hK : K < L.blobLen) (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hwa : a.toNat + 8 ≤ 2 ^ 64)
    (hdisj : L.codeBase.toNat + L.blobLen ≤ a.toNat ∨ a.toNat + 8 ≤ L.codeBase.toNat) :
    (m.storeWord a v).mem (L.codeBase + BitVec.ofNat 64 K) = m.mem (L.codeBase + BitVec.ofNat 64 K) := by
  have hy := blobAddr_toNat L K hK hblob
  apply Rv64i.storeWord_mem_outside m a v _ hwa
  omega

/-- **`Installed` is preserved by a store off the blob.** The store's 8 bytes
    miss every instruction byte (`hseg` puts the code below `segStart`) and every
    data byte, so the trusted fetch/data reads are unchanged. -/
theorem Installed_storeWord_off_blob (L : Layout) (m : State) (a v : Word)
    (hinst : Installed L m)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hwa : a.toNat + 8 ≤ 2 ^ 64)
    (hdisj : L.codeBase.toNat + L.blobLen ≤ a.toNat ∨ a.toNat + 8 ≤ L.codeBase.toNat) :
    Installed L (m.storeWord a v) := by
  obtain ⟨hcode, hdata⟩ := hinst
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · -- code: the 4 fetch bytes at codeBase+4j … +3 are all below segStart ≤ blobLen
    have hbl : L.segStart ≤ L.blobLen := by
      simp only [Layout.blobLen]; omega
    have e0 : (m.storeWord a v).mem (L.codeBase + BitVec.ofNat 64 (4 * j))
                = m.mem (L.codeBase + BitVec.ofNat 64 (4 * j)) :=
      mem_storeWord_off_blob L m a v (4 * j) (by omega) hblob hwa hdisj
    -- the other three bytes: rewrite `+ ofNat(4j) + c` as `+ ofNat(4j + c)`
    have key : ∀ c : Nat, c < 4 →
        (m.storeWord a v).mem (L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c)
          = m.mem (L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c) := by
      intro c hc
      have : L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c
               = L.codeBase + BitVec.ofNat 64 (4 * j + c) := by
        rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [this]
      exact mem_storeWord_off_blob L m a v (4 * j + c) (by omega) hblob hwa hdisj
    rw [← hcode j hj]
    apply congrArg decode
    -- `P + 1` is defeq to `P + BitVec.ofNat 64 1`, so `key` applies directly
    exact fetch32_pc_congr _ _ _ e0 (key 1 (by omega)) (key 2 (by omega)) (key 3 (by omega))
  · -- data: the byte at codeBase+segStart+i is inside the blob (i < dataLen)
    have : L.segStart + i < L.blobLen := by
      simp only [Layout.blobLen]; omega
    rw [mem_storeWord_off_blob L m a v (L.segStart + i) this hblob hwa hdisj]
    exact hdata i hi

/-! ## §5 — the payoff: a slot store mirrors `rset`, preserving `StInv`.

    Writing IL register `r`'s value `v` into its machine slot (`storeWord` at
    `sp + slotOff r`) exactly realises the IL `rset r v`: `StInv` is re-established
    for `(s.rset r v, m.storeWord … v)`. Everything else is untouched — `sp ≡ x2`
    (the store hits memory, not `x2`), the const blob survives (`hbd` puts the
    frame hole off the blob), and off-`MachPriv` memory is unchanged because the
    slot lives inside this activation's hole.

    The three "well-formedness" hypotheses (`hnw`/`hseg`/`hblob`/`hbd`) are the
    frame- and blob-placement facts that `SimPre` discharges in Phases 4/5; kept
    explicit here so the slot algebra stands alone. -/
theorem StInv_store_slot (L : Layout) (fd : FunDef) (holes : List Hole)
    (s : St) (m : State) (r : Nat) (v : Word)
    (hinv : StInv L fd holes s m)
    (hr1 : 1 ≤ r) (hrm : r ≤ maxRegF fd)
    (hnw  : s.sp.toNat + userOff fd ≤ 2 ^ 64)
    (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.codeBase.toNat + L.blobLen ≤ 2 ^ 64)
    (hbd : L.codeBase.toNat + L.blobLen ≤ s.sp.toNat
             ∨ s.sp.toNat + userOff fd ≤ L.codeBase.toNat) :
    StInv L fd holes (s.rset r v) (m.storeWord (s.sp + BitVec.ofNat 64 (slotOff r)) v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
  have hr0 : r ≠ 0 := by omega
  have hslot_r : slotOff r + 8 ≤ userOff fd := slotOff_add8_le_userOff fd r hrm
  have ha_toNat : (s.sp + BitVec.ofNat 64 (slotOff r)).toNat = s.sp.toNat + slotOff r :=
    slotAddr_toNat s.sp r (by omega)
  have hwa : (s.sp + BitVec.ofNat 64 (slotOff r)).toNat + 8 ≤ 2 ^ 64 := by rw [ha_toNat]; omega
  have hbnd_r : s.sp.toNat + slotOff r + 8 ≤ 2 ^ 64 := by omega
  -- record-update / store algebra: rset keeps sp+mem, storeWord keeps regs
  have hsp' : (s.rset r v).sp = s.sp := by simp [LowIR.Prog.St.rset, hr0]
  have hmem' : (s.rset r v).mem = s.mem := by simp [LowIR.Prog.St.rset, hr0]
  have hreg2 : (m.storeWord (s.sp + BitVec.ofNat 64 (slotOff r)) v).rget 2 = m.rget 2 := by
    simp [State.storeWord, State.storeByte, State.rget]
  have hget_same : (s.rset r v).rget r = v := by simp [LowIR.Prog.St.rget, LowIR.Prog.St.rset, hr0]
  have hget_ne : ∀ r', r' ≠ r → (s.rset r v).rget r' = s.rget r' := by
    intro r' hne; simp [LowIR.Prog.St.rget, LowIR.Prog.St.rset, hr0, hne]
  -- the current activation's hole is in `holes`, so ¬MachPriv rules it out
  have hhole_mem : (s.sp, userOff fd) ∈ holes := by
    cases holes with
    | nil => simp at h5
    | cons h0 t =>
        simp only [List.head?_cons, Option.some.injEq] at h5
        rw [← h5]; exact List.mem_cons_self
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sp ≡ x2
    rw [hsp', hreg2]; exact h1
  · -- slot invariant
    intro r' hr1' hrm'
    rw [hsp']
    -- decidable case split (bare `by_cases` routes through `Classical`)
    cases Nat.decEq r' r with
    | isTrue hrr =>
      subst hrr
      rw [hget_same]; exact (loadWord_store_slot_same m s.sp v r').symm
    | isFalse hrr =>
      have hbnd_r' : s.sp.toNat + slotOff r' + 8 ≤ 2 ^ 64 := by
        have := slotOff_add8_le_userOff fd r' hrm'; omega
      rw [hget_ne r' hrr, loadWord_store_slot_ne m s.sp v r r' (Ne.symm hrr) hbnd_r hbnd_r']
      exact h2 r' hr1' hrm'
  · -- Installed preserved
    apply Installed_storeWord_off_blob L m _ v h3 hseg hblob hwa
    rw [ha_toNat]
    rcases hbd with hbd | hbd
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · -- off-MachPriv memory agreement
    intro a hna
    rw [hmem', h4 a hna]
    symm
    apply Rv64i.storeWord_mem_outside m _ v a hwa
    rw [ha_toNat]
    have hnr : ¬ memRange a s.sp (userOff fd) := fun hc =>
      hna (Or.inr ⟨(s.sp, userOff fd), hhole_mem, hc⟩)
    -- split the disjunction constructively (bare `omega` on `¬(_ ∧ _)` pulls in
    -- `Classical.choice` — the gotcha memory), keeping axioms at `propext/Quot.sound`
    rcases Nat.lt_or_ge a.toNat s.sp.toNat with hlt | hge
    · exact Or.inl (by omega)
    · have hnlt : ¬ a.toNat < s.sp.toNat + userOff fd := fun hh => hnr ⟨hge, hh⟩
      exact Or.inr (by omega)
  · -- current hole unchanged
    rw [hsp']; exact h5
  · -- sp alignment unchanged
    rw [hsp']; exact h6

end LowIR.ProgSim
