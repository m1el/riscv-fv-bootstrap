import LowIR.ProgSim.Defs
import LowIR.ProgSim.EncodeFacts
import LowIR.ProgSim.CtrlSim

/-!
# Phase 2 (start) — the assembler layer: `Installed`'s code half from the bytes

Phase 1 (`EncodeFacts`) proved `decode (encode i) = i`. This file closes the
other side of `Installed`'s code conjunct: the machine's `fetch32` over the
assembled byte stream (`asmBytes`) at instruction slot `j` recovers
`encode instrs[j]`, so with Phase 1 it decodes to `instrs[j]`.

Two pieces: (a) the little-endian **reassembly** — `fetch32` of the four
`insBytes` of `w` is `w`; (b) the **flatten indexing** — `asmBytes` byte
`4j + k` is `insBytes instrs[j]` byte `k`. Composed: `installed_code_of_mem`,
exactly `Installed`'s code conjunct for any memory holding `asmBytes L.instrs`
at `codeBase` (given every emitted instruction is `WF`).
-/

open LowIR Rv64i
open LowIR.Prog (dataSegment Env FunDef Name)
open LowIR.Compile (userOff)

namespace LowIR.ProgSim.AsmFacts

open EncodeFacts (WF decode_encode)

/-! ## §1 Little-endian reassembly. -/

/-- `fetch32`'s little-endian recombination of the four bytes of a 32-bit word
    is that word. -/
theorem fetch32_reassemble (w : BitVec 32) :
    (w.setWidth 8).setWidth 32 ||| ((w >>> 8).setWidth 8).setWidth 32 <<< 8
    ||| ((w >>> 16).setWidth 8).setWidth 32 <<< 16
    ||| ((w >>> 24).setWidth 8).setWidth 32 <<< 24 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
             BitVec.getLsbD_ushiftRight]
  rcases Nat.lt_or_ge i 8 with h8 | h8
  · simp only [h8, hi, show i < 16 by omega, show i < 24 by omega, decide_true, Bool.true_and,
               Bool.not_true, Bool.false_and, Bool.and_false, Bool.or_false]
  · rcases Nat.lt_or_ge i 16 with h16 | h16
    · have e : 8 + (i - 8) = i := by omega
      simp only [hi, h16, e, show i < 24 by omega, decide_true, Bool.true_and,
                 show ¬ i < 8 by omega, decide_false, Bool.not_false, Bool.not_true,
                 Bool.false_and, Bool.and_false, Bool.and_true, show i - 8 < 32 by omega,
                 show i - 8 < 8 by omega, Bool.or_false, Bool.false_or]
    · rcases Nat.lt_or_ge i 24 with h24 | h24
      · have e : 16 + (i - 16) = i := by omega
        simp only [hi, h24, e, decide_true, Bool.true_and, show ¬ i < 8 by omega,
                   show ¬ i < 16 by omega, decide_false, Bool.not_false, Bool.not_true,
                   Bool.false_and, Bool.and_false, Bool.and_true, show i - 16 < 32 by omega,
                   show i - 16 < 8 by omega, show ¬ i - 8 < 8 by omega, Bool.or_false,
                   Bool.false_or]
      · have e : 24 + (i - 24) = i := by omega
        simp only [hi, e, decide_true, Bool.true_and, show ¬ i < 8 by omega,
                   show ¬ i < 16 by omega, show ¬ i < 24 by omega, decide_false, Bool.not_false,
                   Bool.false_and, Bool.and_false, Bool.and_true, show i - 24 < 32 by omega,
                   show i - 24 < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
                   Bool.or_false, Bool.false_or]

/-- If memory holds the four `insBytes i` at `base .. base+3`, then `fetch32`
    from `base` is `encode i`. -/
theorem fetch32_encode (m : State) (base : Word) (i : Instr)
    (h0 : m.mem base = (encode i).setWidth 8)
    (h1 : m.mem (base + 1) = ((encode i) >>> 8).setWidth 8)
    (h2 : m.mem (base + 2) = ((encode i) >>> 16).setWidth 8)
    (h3 : m.mem (base + 3) = ((encode i) >>> 24).setWidth 8) :
    fetch32 { m with pc := base } = encode i := by
  simp only [fetch32, h0, h1, h2, h3]
  exact fetch32_reassemble (encode i)

/-! ## §2 Flatten indexing: `asmBytes` byte `4j + k` is `insBytes instrs[j]` byte `k`. -/

theorem insBytes_length (i : Instr) : (insBytes i).length = 4 := rfl

/-- `asmBytes` is a flatten of length-4 blocks: byte `4j + k` (`k < 4`) is byte
    `k` of `insBytes` of the `j`-th instruction. -/
theorem asmBytes_getElem? (is : List Instr) :
    ∀ (j k : Nat), j < is.length → k < 4 →
      (asmBytes is)[4 * j + k]? = (insBytes (is.getD j .unknown))[k]? := by
  induction is with
  | nil => intro j k hj _; exact absurd hj (by simp)
  | cons i rest ih =>
    intro j k hj hk
    have hasm : asmBytes (i :: rest) = insBytes i ++ asmBytes rest := by
      simp only [asmBytes, List.map_cons, List.flatten_cons]
    rw [hasm]
    cases j with
    | zero =>
      have hlt : 4 * 0 + k < (insBytes i).length := by rw [insBytes_length]; omega
      rw [List.getElem?_append_left hlt]; simp
    | succ j' =>
      have hge : (insBytes i).length ≤ 4 * (j' + 1) + k := by rw [insBytes_length]; omega
      have he : 4 * (j' + 1) + k - (insBytes i).length = 4 * j' + k := by
        rw [insBytes_length]; omega
      rw [List.getElem?_append_right hge, he, ih j' k (by simpa using hj) hk]
      rfl

/-- Byte-level form: memory holding `asmBytes` byte `4j+k` equals the LE byte of
    `encode instrs[j]`. -/
theorem asmBytes_getD (is : List Instr) (j k : Nat) (hj : j < is.length) (hk : k < 4) :
    (asmBytes is).getD (4 * j + k) 0 = (insBytes (is.getD j .unknown)).getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, asmBytes_getElem? is j k hj hk]

theorem asmBytes_length (is : List Instr) : (asmBytes is).length = 4 * is.length := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
    have : asmBytes (i :: rest) = insBytes i ++ asmBytes rest := by
      simp only [asmBytes, List.map_cons, List.flatten_cons]
    rw [this, List.length_append, insBytes_length, ih, List.length_cons]; omega

/-! ## §3 `Installed`'s code half from a memory holding `asmBytes`. -/

/-- The core Phase-2 code lemma: if `m`'s memory holds `asmBytes L.instrs` at
    `L.codeBase` and every emitted instruction is `WF`, then every instruction
    slot decodes correctly — exactly `Installed`'s code conjunct. -/
theorem installed_code_of_mem (L : Layout) (m : State)
    (hwf : ∀ i, i ∈ L.instrs → WF i)
    (hmem : ∀ n, n < (asmBytes L.instrs).length →
              m.mem (L.codeBase + BitVec.ofNat 64 n) = (asmBytes L.instrs).getD n 0)
    (j : Nat) (hj : j < L.instrs.length) :
    decode (fetch32 { m with pc := L.codeBase + BitVec.ofNat 64 (4 * j) }) = L.instrs[j]'hj := by
  have hidx : L.instrs.getD j .unknown = L.instrs[j]'hj := (List.getElem_eq_getD Instr.unknown).symm
  -- the four little-endian bytes at slot j
  have byteEq : ∀ k, k < 4 →
      m.mem (L.codeBase + BitVec.ofNat 64 (4 * j + k)) = (insBytes L.instrs[j]).getD k 0 := by
    intro k hk
    rw [hmem (4 * j + k) (by rw [asmBytes_length]; omega), asmBytes_getD L.instrs j k hj hk, hidx]
  -- address realignment: base + literal k = codeBase + ofNat 64 (4j + k)
  have hbase : ∀ k : Nat, L.codeBase + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k
      = L.codeBase + BitVec.ofNat 64 (4 * j + k) := by
    intro k; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [fetch32_encode m (L.codeBase + BitVec.ofNat 64 (4 * j)) L.instrs[j]
        (by have := byteEq 0 (by omega); simpa using this)
        (by have := byteEq 1 (by omega)
            rw [show (1 : Word) = BitVec.ofNat 64 1 from rfl, hbase 1]; simpa using this)
        (by have := byteEq 2 (by omega)
            rw [show (2 : Word) = BitVec.ofNat 64 2 from rfl, hbase 2]; simpa using this)
        (by have := byteEq 3 (by omega)
            rw [show (3 : Word) = BitVec.ofNat 64 3 from rfl, hbase 3]; simpa using this)]
  exact decode_encode _ (hwf _ (List.getElem_mem hj))

/-- **`Installed` from a memory holding the blob.** Decoupled into the code and
    data byte hypotheses a `loadMem`-style memory supplies directly: `hcode` for
    `asmBytes L.instrs` at `codeBase`, `hdata` for `dataSegment L.data` at
    `codeBase + segStart`. -/
theorem installed_of_mem (L : Layout) (m : State)
    (hwf : ∀ i, i ∈ L.instrs → WF i)
    (hcode : ∀ n, n < (asmBytes L.instrs).length →
               m.mem (L.codeBase + BitVec.ofNat 64 n) = (asmBytes L.instrs).getD n 0)
    (hdata : ∀ i, i < (dataSegment L.data).length →
               m.mem (L.codeBase + BitVec.ofNat 64 (L.segStart + i))
                 = (dataSegment L.data).getD i 0) :
    Installed L m := by
  refine ⟨fun j hj => installed_code_of_mem L m hwf hcode j hj, fun i hi => ?_⟩
  rw [hdata i hi]; exact (List.getElem_eq_getD 0).symm

/-! ## §4 A trivial flat obligation: `pad = userPad` satisfies `hpad`. -/

/-- `userPad` (prog_sim's `pad`) satisfies the `call` case's `hpad` obligation. -/
theorem userPad_eq (env : Env) (g : Name) (gd : FunDef)
    (h : List.lookup g env = some gd) : userPad env g = userOff gd := by
  simp only [userPad, h, Option.elim]

/-! ## §5 The remaining flat obligations, discharged from `layoutOf`/the guard.

    `lower_sim_cf`/`prog_sim` take the flat compile-time hypotheses `hdat`,
    `hstackLo`, `hdbase`, `hdpos`, `halign`, `hfn` (RESUME-CALL §C4, RESUME-PROGSIM
    §Phase-2). This section closes the three that follow from `layoutOf` and the
    compiler's own data guard alone: `hdat` (clen synth range), `hstackLo` (the
    stackLo field), and `hdbase` (the data-address correspondence). `hdpos`
    (needs a blob-size bound), `halign` (codeBase alignment — a `prog_sim`
    hypothesis) and `hfn`/`hem` (the layout↔`Emitted` correspondence — its
    prologue/epilogue-resolve half is done in §6 below) are still owed. -/

open LowIR.Prog (Program Data dataOffsetsFrom dbaseOf dataOffsetsFrom_shift)
open LowIR.Compile (compileProgT)

/-! ### `hstackLo` — the layout's stack floor is the requested one. -/

/-- `layoutOf` copies its `stackLo` argument into the `Layout` field verbatim. -/
theorem layoutOf_stackLo {P : Program} {entry : Name} {cb slo : Word} {L : Layout}
    (h : layoutOf P entry cb slo = some L) : L.stackLo = slo := by
  unfold layoutOf at h
  cases hc : compileProgT P entry with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some t => rw [hc] at h; simp only [Option.some.injEq] at h; rw [← h]

/-! ### `hdat` — the clen data-length synth stays in the 12-bit signed range. -/

/-- A looked-up data object's length is bounded by the whole-list bound (or the
    lookup misses, giving `0`). Mathlib-free, `BEq`-agnostic: induct on the list
    rather than route through membership (no `LawfulBEq` needed). -/
theorem lookup_len_lt (data : Data) (b : Nat) (d : Name)
    (hwf : data.all (fun x => x.2.length < b)) :
    (((List.lookup d data).map (·.length)).getD 0 : Nat) < b ∨ List.lookup d data = none := by
  induction data with
  | nil => right; rfl
  | cons hd tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    rw [List.lookup_cons]
    by_cases he : (d == hd.1) = true
    · left; simp only [he, Option.map_some, Option.getD_some]; exact of_decide_eq_true hwf.1
    · simp only [he]; exact ih hwf.2

/-- `compileProgT = some` forces the data guard (`length < 2^22`) — the tightened
    bound (Compile.lean, 2026-07-05) that keeps `clen`'s `synthConst` in range. -/
theorem compileProgT_dataBound {P : Program} {entry : Name} {t}
    (h : compileProgT P entry = some t) : P.data.all (fun d => d.2.length < 2 ^ 22) := by
  unfold compileProgT at h
  cases hg : (LowIR.Prog.wfProgram P && P.env.all (fun nf => LowIR.Compile.fnOk nf.2)
       && (List.lookup entry P.env).isSome
       && P.data.all (fun d => d.2.length < 2 ^ 22)) with
  | false => rw [hg] at h; simp at h
  | true => simp only [Bool.and_eq_true] at hg; exact hg.2

/-- **`hdat`.** For any program whose data satisfies the compiler guard, every
    object's `clen` length synthesizes within the 12-bit signed immediate window
    (`-2048 ≤ synthHi ≤ 2047`) — so `run_synth` fires. -/
theorem clen_synthOk {P : Program} (hwf : P.data.all (fun d => d.2.length < 2 ^ 22)) (d : Name) :
    -2048 ≤ synthHi (((List.lookup d P.data).map (·.length)).getD 0)
    ∧ synthHi (((List.lookup d P.data).map (·.length)).getD 0) ≤ 2047 := by
  cases h : List.lookup d P.data with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    unfold synthHi synthLo; constructor <;> omega
  | some bs =>
    have hb : (bs.length : Nat) < 2 ^ 22 := by
      rcases lookup_len_lt P.data (2 ^ 22) d hwf with hl | hn
      · rw [h] at hl; simpa using hl
      · rw [h] at hn; exact absurd hn (by simp)
    simp only [Option.map_some, Option.getD_some]
    have : ((bs.length : Nat) : Int) < 2 ^ 22 := by exact_mod_cast hb
    unfold synthHi synthLo; constructor <;> omega

/-! ### `hdbase` — the IL data base agrees with the layout's `dpos`. -/

/-- The `dpos : Name → Nat` prog_sim feeds `emitCF`: the byte offset of object
    `d` inside the blob (`segStart` + its offset within the data segment). This IS
    the compiler's `resolveOne` table `dataOffsetsFrom (pad8 codeEnd)` — matched to
    `segStart` by the (owed) layout correspondence, via `dataOffsetsFrom_shift`. -/
def dposOf (L : Layout) : Name → Nat := fun d =>
  (List.lookup d (dataOffsetsFrom L.segStart L.data)).getD 0

/-- **`hdbase`.** The IL address map `dbaseOf (codeBase + segStart)` lands each
    object at `codeBase + dposOf d`, exactly `emitCF`'s cref target. -/
theorem dbaseOf_dposOf (L : Layout) (d : Name) (a : Word)
    (h : dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) L.data d = some a) :
    a = L.codeBase + BitVec.ofNat 64 (dposOf L d) := by
  unfold dbaseOf dposOf at *
  cases ho : List.lookup d (dataOffsetsFrom 0 L.data) with
  | none => rw [ho] at h; exact absurd h (by simp)
  | some off =>
    rw [ho] at h; simp only [Option.map_some, Option.some.injEq] at h
    have hshift : List.lookup d (dataOffsetsFrom L.segStart L.data)
        = (List.lookup d (dataOffsetsFrom 0 L.data)).map (L.segStart + ·) := by
      have := dataOffsetsFrom_shift (n := d) L.segStart 0 L.data
      simpa using this
    rw [hshift, ho]
    simp only [Option.map_some, Option.getD_some]
    rw [← h, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- Each data object's byte offset lies within the blob: `dposOf L d ≤ blobLen`. -/
theorem dposOf_le_blobLen (L : Layout) (d : Name) : dposOf L d ≤ L.blobLen := by
  unfold dposOf Layout.blobLen
  cases hlk : List.lookup d (dataOffsetsFrom L.segStart L.data) with
  | none => simp
  | some off =>
      simp only [hlk, Option.getD_some]
      exact LowIR.Prog.dataOffsetsFrom_off_le L.segStart L.data hlk

/-- **`hdpos`** from the blob-size bound: every data offset is `< 2²⁰`. -/
theorem dposOf_lt (L : Layout) (hblob : L.blobLen < 2 ^ 20) (d : Name) :
    dposOf L d < 2 ^ 20 :=
  Nat.lt_of_le_of_lt (dposOf_le_blobLen L d) hblob

/-- The code bytes fit within the blob: `4·|instrs| ≤ blobLen` (given `hseg`). -/
theorem codeLen_le_blobLen (L : Layout) (hseg : 4 * L.instrs.length ≤ L.segStart) :
    4 * L.instrs.length ≤ L.blobLen := by
  unfold Layout.blobLen; omega

/-- **`hcode`** (the `fn_hfn`/`hbnd` blob bound) from the blob-size bound. -/
theorem codeLen_lt (L : Layout) (hseg : 4 * L.instrs.length ≤ L.segStart)
    (hblob : L.blobLen < 2 ^ 20) : 4 * L.instrs.length < 2 ^ 20 :=
  Nat.lt_of_le_of_lt (codeLen_le_blobLen L hseg) hblob

/-! ## §6 `hfn`/`hem` foundation — the prologue/epilogue resolve correspondence.

    `hfn`/`hem` state that the compiler's RESOLVED stream (`compileProgT`'s output,
    = `L.instrs`), sliced at each function's byte position, equals
    `prologueI gd ++ emitCF … gd.body ++ epilogueI gd` (RESUME-CALL §C4). The full
    correspondence needs the `layout`-flatten structural arithmetic (which slice of
    `L.instrs` a function occupies) AND the `lower`↔`emitCF` label-resolution
    induction (the crux). This section closes the two SELF-CONTAINED halves that
    need neither: the machine `resolveOne` over `Compile.prologue`/`epilogue`
    (both all-`.ins`, position-independent) flattens to exactly `prologueI`/
    `epilogueI`. These are the leaf inputs the per-function `hfn` assembly consumes.

    ⚠ **STILL OWED for `hfn`/`hem` (the big one, next session):** (a) the
    `layout`/`layoutItems` position arithmetic tying `fnPos g` to the slice of the
    resolved stream, and (b) `resolveOne`-over-`lower dat [] [] epi gd.body`
    = `emitCF P.data dpos fnPos [] [] epiPos bodyPos gd.body` — the label-resolution
    induction (the `matchesRealProg` #guard is its decidable shadow). -/

open LowIR.Compile (prologue epilogue layoutItems resolveOne symSize storeSlot loadSlot
                    SymInstr A SP RA T0 T1 totalFrame maxRegF slotOff)

/-- The instruction(s) a `.ins`/`.label` `SymInstr` resolves to (position-free):
    `.ins i ↦ [i]`, everything else `↦ []` (only `.label`, in a well-formed
    all-`.ins`/`.label` stream). -/
def insUnwrap : SymInstr → List Instr
  | .ins i => [i]
  | _      => []

/-- A `SymInstr` is a concrete instruction or a (0-byte) label marker — the two
    cases `resolveOne` handles position-independently. -/
def isInsOrLabel : SymInstr → Bool
  | .ins _   => true
  | .label _ => true
  | _        => false

/-- For a stream of only `.ins`/`.label` items, `resolveOne` is position-independent
    and maps each item to its `insUnwrap`. -/
theorem resolve_ins_mapM (lbls fns dats : List _) :
    ∀ (items : List SymInstr) (pos : Nat),
      items.all isInsOrLabel = true →
      (layoutItems items pos).1.mapM (resolveOne lbls fns dats)
        = some (items.map insUnwrap) := by
  intro items
  induction items with
  | nil => intro pos _; rfl
  | cons si rest ih =>
    intro pos hall
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hsi, hrest⟩ := hall
    cases si with
    | label l =>
      have hflat : (layoutItems (.label l :: rest) pos).1
          = (pos, SymInstr.label l) :: (layoutItems rest pos).1 := by
        simp only [layoutItems]
      rw [hflat, List.mapM_cons]
      simp only [show resolveOne lbls fns dats (pos, SymInstr.label l) = some [] from rfl,
                 ih pos hrest, List.map_cons, insUnwrap]
      rfl
    | ins i =>
      have hflat : (layoutItems (.ins i :: rest) pos).1
          = (pos, SymInstr.ins i) :: (layoutItems rest (pos + symSize (.ins i))).1 := by
        simp only [layoutItems]
      rw [hflat, List.mapM_cons]
      simp only [show resolveOne lbls fns dats (pos, SymInstr.ins i) = some [i] from rfl,
                 ih _ hrest, List.map_cons, insUnwrap]
      rfl
    | br c a b l => exact absurd hsi (by simp [isInsOrLabel])
    | jmp l => exact absurd hsi (by simp [isInsOrLabel])
    | callf f => exact absurd hsi (by simp [isInsOrLabel])
    | cref d => exact absurd hsi (by simp [isInsOrLabel])

/-! ### Unwrap algebra: `flatMap insUnwrap` distributes over the emit builders. -/

theorem insUnwrap_flatMap_append (l₁ l₂ : List SymInstr) :
    (l₁ ++ l₂).flatMap insUnwrap = l₁.flatMap insUnwrap ++ l₂.flatMap insUnwrap := by
  rw [List.flatMap_append]

theorem insUnwrap_map_ins {α} (l : List α) (g : α → Instr) :
    (l.map (fun x => SymInstr.ins (g x))).flatMap insUnwrap = l.map g := by
  induction l with
  | nil => rfl
  | cons x t ih => simp only [List.map_cons, List.flatMap_cons, insUnwrap, ih, List.singleton_append]

theorem storeSlot_unwrap (r t : Prog.Reg) : (storeSlot r t).flatMap insUnwrap = storeSlotI r t := by
  unfold storeSlot storeSlotI
  by_cases h : r = 0 <;> simp [h, insUnwrap]

theorem loadSlot_unwrap (r t : Prog.Reg) : (loadSlot r t).flatMap insUnwrap = loadSlotI r t := by
  unfold loadSlot loadSlotI
  by_cases h : r = 0 <;> simp [h, insUnwrap]

/-- Push `flatMap insUnwrap` through an outer `flatMap` when the inner builder
    unwraps pointwise. -/
theorem insUnwrap_flatMap_flatMap {α} (l : List α) (g : α → List SymInstr) (gi : α → List Instr)
    (h : ∀ x, (g x).flatMap insUnwrap = gi x) :
    (l.flatMap g).flatMap insUnwrap = l.flatMap gi := by
  induction l with
  | nil => rfl
  | cons x t ih => rw [List.flatMap_cons, List.flatMap_cons, insUnwrap_flatMap_append, h, ih]

/-! ### Prologue / epilogue unwrap: the symbolic builder ↦ the resolved list. -/

theorem prologue_unwrap (fd : FunDef) :
    (prologue fd).flatMap insUnwrap = prologueI fd := by
  unfold prologue prologueI prologuePreI frameZeroI
  simp only [insUnwrap_flatMap_append]
  have hhead : ([SymInstr.ins (Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int)))),
                 SymInstr.ins (Instr.sd SP RA 0)]).flatMap insUnwrap
      = [Instr.addi SP SP (BitVec.ofInt 12 (-(totalFrame fd : Int))), Instr.sd SP RA 0] := by
    simp [insUnwrap]
  have hparams : ((fd.params.toList.zipIdx.flatMap (fun pi => storeSlot pi.1 (A pi.2)))).flatMap insUnwrap
      = fd.params.toList.zipIdx.flatMap (fun pi => storeSlotI pi.1 (A pi.2)) :=
    insUnwrap_flatMap_flatMap _ _ _ (fun pi => storeSlot_unwrap pi.1 (A pi.2))
  have hzero : (((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).map
       (fun r => SymInstr.ins (Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r))))).flatMap insUnwrap
      = ((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !fd.params.toList.contains r && r != fd.frameReg)).map
       (fun r => Instr.sd SP 0 (BitVec.ofNat 12 (slotOff r))) :=
    insUnwrap_map_ins _ _
  have hframeReg : (if fd.frameReg = 0 then [] else
        [SymInstr.ins (Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd)))]
          ++ storeSlot fd.frameReg T0).flatMap insUnwrap
      = (if fd.frameReg = 0 then [] else
        [Instr.addi T0 SP (BitVec.ofNat 12 (userOff fd))] ++ storeSlotI fd.frameReg T0) := by
    by_cases h : fd.frameReg = 0
    · simp [h]
    · simp only [if_neg h, storeSlot_unwrap, insUnwrap, List.flatMap_cons, List.singleton_append]
  have hfz : ((List.range (fd.frameSize / 8)).map
       (fun i => SymInstr.ins (Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i))))).flatMap insUnwrap
      = (List.range (fd.frameSize / 8)).map
       (fun i => Instr.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i))) :=
    insUnwrap_map_ins _ _
  rw [hhead, hparams, hzero, hframeReg, hfz]

theorem epilogue_unwrap (fd : FunDef) :
    (epilogue fd).flatMap insUnwrap = epilogueI fd := by
  unfold epilogue epilogueI
  simp only [insUnwrap_flatMap_append]
  have hrets : ((fd.rets.toList.zipIdx.flatMap (fun ri => loadSlot ri.1 (A ri.2)))).flatMap insUnwrap
      = fd.rets.toList.zipIdx.flatMap (fun ri => loadSlotI ri.1 (A ri.2)) :=
    insUnwrap_flatMap_flatMap _ _ _ (fun ri => loadSlot_unwrap ri.1 (A ri.2))
  have htail : ([SymInstr.ins (Instr.ld RA SP 0),
                 SymInstr.ins (Instr.addi SP SP (BitVec.ofNat 12 (totalFrame fd))),
                 SymInstr.ins (Instr.jalr 0 RA 0)]).flatMap insUnwrap
      = [Instr.ld RA SP 0, Instr.addi SP SP (BitVec.ofNat 12 (totalFrame fd)), Instr.jalr 0 RA 0] := by
    simp [insUnwrap]
  rw [hrets, htail]

theorem storeSlot_all_ins (r t : Prog.Reg) : (storeSlot r t).all isInsOrLabel = true := by
  unfold storeSlot; by_cases h : r = 0 <;> simp [h, isInsOrLabel]

theorem loadSlot_all_ins (r t : Prog.Reg) : (loadSlot r t).all isInsOrLabel = true := by
  unfold loadSlot; by_cases h : r = 0 <;> simp [h, isInsOrLabel]

theorem prologue_all_ins (fd : FunDef) : (prologue fd).all isInsOrLabel = true := by
  unfold prologue
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [isInsOrLabel]
  · simp [List.all_flatMap, storeSlot_all_ins]
  · simp [List.all_map, isInsOrLabel]
  · by_cases h : fd.frameReg = 0 <;> simp [h, isInsOrLabel, storeSlot_all_ins]
  · simp [List.all_map, isInsOrLabel]

theorem epilogue_all_ins (fd : FunDef) : (epilogue fd).all isInsOrLabel = true := by
  unfold epilogue
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨by simp [List.all_flatMap, loadSlot_all_ins], by simp [isInsOrLabel]⟩

/-! ### The payoff: `resolveOne`-flatten of the prologue/epilogue = `prologueI`/`epilogueI`. -/

/-- **prologue resolve correspondence.** Resolving the compiler's symbolic
    prologue at any position, then flattening, yields exactly `prologueI fd`. -/
theorem prologue_resolves (fd : FunDef) (lbls fns dats : List _) (pos : Nat) :
    ((layoutItems (prologue fd) pos).1.mapM (resolveOne lbls fns dats)).map List.flatten
      = some (prologueI fd) := by
  rw [resolve_ins_mapM lbls fns dats _ pos (prologue_all_ins fd), Option.map_some,
      ← List.flatMap_def, prologue_unwrap]

/-- **epilogue resolve correspondence.** Likewise for the epilogue. -/
theorem epilogue_resolves (fd : FunDef) (lbls fns dats : List _) (pos : Nat) :
    ((layoutItems (epilogue fd) pos).1.mapM (resolveOne lbls fns dats)).map List.flatten
      = some (epilogueI fd) := by
  rw [resolve_ins_mapM lbls fns dats _ pos (epilogue_all_ins fd), Option.map_some,
      ← List.flatMap_def, epilogue_unwrap]

end LowIR.ProgSim.AsmFacts
