/-
  LowIR.Compile — Prog → RV64I instructions (EXECUTABLE, UNVERIFIED first cut).

  Strategy: MEMORY-LOCALS (-O0). Every IL register gets an 8-byte slot in the
  function's machine frame; no register allocation. Correctness-first — the
  point is a differential-testing target for the D7/D8 semantics, and later the
  subject of `compile_sim`-style theorems (performance is a non-goal, N9).

  Machine frame (grows down; all offsets sp-relative, sp = x2 after prologue):

        sp + 0                  : saved ra
        sp + 8*(1+r)            : slot for IL register r   (r = 0..maxReg)
        sp + 8*(maxReg+2)       : user frame (frameSize bytes) — the address
                                  handed to the IL `frameReg`
        total = 8*(maxReg+2) + frameSize   (must fit imm12: ≤ 2000, checked)

  Physical registers: x2=sp, x1=ra, x5/x6 = t0/t1 scratch, x10..x17 = a0..a7
  argument/return marshalling (so argc,rvc ≤ 8, checked). Nothing is live
  across an IL statement except the slots, so calls need no caller-save logic.

  IL zero-init is matched EXACTLY: the prologue `sd x0` into every non-param,
  non-frameReg slot (differential tests stay honest; definite-assignment
  optimization comes later).

  Pipeline: lower to `SymInstr` (labels symbolic, calls by name) → lay out the
  whole program (all instructions are 4 bytes) → resolve branches/jumps/calls
  to relative offsets (range-checked) → `Rv64i.Instr` list. Encoding to bytes
  reuses `LowIR.encode`/`asmBytes`. Entry convention: the program starts with
  a single `jal ra, <entry>` stub at `codeBase`; when the entry function
  returns, pc = codeBase+4 — run the machine with `runFuel (codeBase+4)`.
-/
import LowIR.Prog

namespace LowIR.Compile

open LowIR (Cond condInstr jal0)
open LowIR.Prog (Reg Name FunDef Env Data Program wfProgram pad8 dataOffsetsFrom dataSegment)
open Rv64i (Word Byte Instr)

/-- The IL being compiled (the parent `LowIR.Stmt` also exists — be explicit). -/
local notation "PStmt" => LowIR.Prog.Stmt

/-! ### Physical register roles -/

def SP : Reg := 2
def RA : Reg := 1
def T0 : Reg := 5
def T1 : Reg := 6
/-- Argument/return register `a_i` = x10+i. -/
def A (i : Nat) : Reg := 10 + i

/-! ### Symbolic instructions -/

/-- Position-independent instruction stream: concrete instructions, label
    markers (emit nothing), and label/name-relative control transfers. -/
inductive SymInstr where
  | ins   (i : Instr)                          -- concrete, position-independent
  | label (l : Nat)                            -- marker (0 bytes)
  | br    (c : Cond) (a b : Reg) (l : Nat)     -- branch (phys regs) to label
  | jmp   (l : Nat)                            -- jal x0, label
  | callf (f : Name)                           -- jal ra, function
  | cref  (d : Name)                           -- T0 := address of data object
deriving Repr

/-! ### Per-function lowering -/

/-- Slot offset of IL register `r` (see frame picture above). -/
def slotOff (r : Reg) : Nat := 8 * (1 + r)

/-- Load IL register `r`'s slot into physical register `t`
    (IL x0 is hardwired zero — never read its slot). -/
def loadSlot (r : Reg) (t : Reg) : List SymInstr :=
  if r = 0 then [.ins (.addi t 0 0)]
  else [.ins (.ld t SP (BitVec.ofNat 12 (slotOff r)))]

/-- Store physical register `t` into IL register `r`'s slot
    (IL writes to x0 are discarded — emit nothing). -/
def storeSlot (r : Reg) (t : Reg) : List SymInstr :=
  if r = 0 then []
  else [.ins (.sd SP t (BitVec.ofNat 12 (slotOff r)))]

/-- Fresh-label supply. -/
abbrev M := StateM Nat
def fresh : M Nat := modifyGet fun n => (n, n + 1)

/-- Materialize the constant `v` (|v| < 2^23) into `t` — a FIXED 3-instruction
    sequence (`v = hi*4096 + lo`, both imm12): layout must not depend on the
    value. -/
def synthConst (t : Reg) (v : Int) : List SymInstr :=
  let lo : Int := ((v + 2048) % 4096) - 2048
  let hi : Int := (v - lo) / 4096
  [.ins (.addi t 0 (BitVec.ofInt 12 hi)), .ins (.slli t t 12),
   .ins (.addi t t (BitVec.ofInt 12 lo))]

/-- Lower one statement. `brks`/`conts` are the enclosing block-end / loop-top
    label stacks (indexed exactly like `brkB`/`contL`'s de Bruijn indices);
    `epi` is this function's epilogue label. `wf` guarantees index ranges and
    call arities; out-of-range lookups fall back to label 0 (never emitted for
    a wf program). -/
def lower (dat : Data) (brks conts : List Nat) (epi : Nat) : PStmt → M (List SymInstr)
  | .skip           => pure []
  | .annot _        => pure []
  | .seq a b        => do pure ((← lower dat brks conts epi a) ++ (← lower dat brks conts epi b))
  | .addi rd rs imm => pure <| loadSlot rs T0 ++ [.ins (.addi T0 T0 imm)] ++ storeSlot rd T0
  | .add  rd r1 r2  => pure <| loadSlot r1 T0 ++ loadSlot r2 T1
                              ++ [.ins (.add T0 T0 T1)] ++ storeSlot rd T0
  | .sub  rd r1 r2  => pure <| loadSlot r1 T0 ++ loadSlot r2 T1
                              ++ [.ins (.sub T0 T0 T1)] ++ storeSlot rd T0
  | .orr  rd r1 r2  => pure <| loadSlot r1 T0 ++ loadSlot r2 T1
                              ++ [.ins (.or T0 T0 T1)] ++ storeSlot rd T0
  | .slli rd rs sh  => pure <| loadSlot rs T0 ++ [.ins (.slli T0 T0 sh)] ++ storeSlot rd T0
  | .srli rd rs sh  => pure <| loadSlot rs T0 ++ [.ins (.srli T0 T0 sh)] ++ storeSlot rd T0
  | .lbu  rd rs imm => pure <| loadSlot rs T0 ++ [.ins (.lbu T0 T0 imm)] ++ storeSlot rd T0
  | .ld   rd rs imm => pure <| loadSlot rs T0 ++ [.ins (.ld T0 T0 imm)] ++ storeSlot rd T0
  | .sb   rb rv imm => pure <| loadSlot rb T0 ++ loadSlot rv T1 ++ [.ins (.sb T0 T1 imm)]
  | .sd   rb rv imm => pure <| loadSlot rb T0 ++ loadSlot rv T1 ++ [.ins (.sd T0 T1 imm)]
  | .ife c a b t e  => do
      let lT ← fresh; let lEnd ← fresh
      let et ← lower dat brks conts epi t
      let ee ← lower dat brks conts epi e
      pure <| loadSlot a T0 ++ loadSlot b T1
           ++ [.br c T0 T1 lT] ++ ee ++ [.jmp lEnd, .label lT] ++ et ++ [.label lEnd]
  | .while c a b body => do
      let lTop ← fresh; let lBody ← fresh; let lEnd ← fresh
      let eb ← lower dat brks (lTop :: conts) epi body
      pure <| [.label lTop] ++ loadSlot a T0 ++ loadSlot b T1
           ++ [.br c T0 T1 lBody, .jmp lEnd, .label lBody]
           ++ eb ++ [.jmp lTop, .label lEnd]
  | .block body     => do
      let lEnd ← fresh
      let eb ← lower dat (lEnd :: brks) conts epi body
      pure <| eb ++ [.label lEnd]
  | .brkB k         => pure [.jmp (brks.getD k 0)]
  | .contL k        => pure [.jmp (conts.getD k 0)]
  | .ret            => pure [.jmp epi]
  | .call _ _ f args rets => do
      let loads  := args.toList.zipIdx.flatMap fun ri => loadSlot ri.1 (A ri.2)
      let stores := rets.toList.zipIdx.flatMap fun ri => storeSlot ri.1 (A ri.2)
      pure <| loads ++ [.callf f] ++ stores
  | .cref rd d      => pure <| [.cref d] ++ storeSlot rd T0
  | .clen rd d      =>
      pure <| synthConst T0 (((List.lookup d dat).map (·.length)).getD 0)
           ++ storeSlot rd T0

/-! ### Frame accounting -/

/-- Largest IL register mentioned in a statement. -/
def maxRegS : PStmt → Nat
  | .skip | .annot _ | .ret | .brkB _ | .contL _ => 0
  | .seq a b          => max (maxRegS a) (maxRegS b)
  | .addi rd rs _     => max rd rs
  | .add  rd r1 r2    => max rd (max r1 r2)
  | .sub  rd r1 r2    => max rd (max r1 r2)
  | .orr  rd r1 r2    => max rd (max r1 r2)
  | .slli rd rs _     => max rd rs
  | .srli rd rs _     => max rd rs
  | .lbu  rd rs _     => max rd rs
  | .ld   rd rs _     => max rd rs
  | .sb   rb rv _     => max rb rv
  | .sd   rb rv _     => max rb rv
  | .ife _ a b t e    => max (max a b) (max (maxRegS t) (maxRegS e))
  | .while _ a b body => max (max a b) (maxRegS body)
  | .block body       => maxRegS body
  | .call _ _ _ args rets =>
      max (args.toList.foldl max 0) (rets.toList.foldl max 0)
  | .cref rd _        => rd
  | .clen rd _        => rd

/-- Largest IL register a function touches (body + declared regs + frameReg). -/
def maxRegF (fd : FunDef) : Nat :=
  max (maxRegS fd.body) <|
  max fd.frameReg <|
  max (fd.params.toList.foldl max 0) (fd.rets.toList.foldl max 0)

/-- Byte offset of the user frame within the machine frame. -/
def userOff (fd : FunDef) : Nat := 8 * (maxRegF fd + 2)

/-- Total machine frame size. -/
def totalFrame (fd : FunDef) : Nat := userOff fd + fd.frameSize

/-- Per-function compilability limits for this first cut: a0..a7 marshalling
    and all slot offsets / frame adjustments within imm12. The `frameSize % 8 = 0`
    clause (added 2026-07-06, like the 2^22 data tightening) closes a real
    soundness gap surfaced by ProgSim Phase 2: the prologue zeroes the user frame
    in 8-byte words (`List.range (frameSize / 8)`), so a non-multiple-of-8
    `frameSize` would leave a tail unzeroed — the machine and the IL `zeroRange`
    would disagree. Every real program already has an 8-aligned frame; the guard
    just makes it a checked precondition (discharges ProgSim `hfn`'s
    `frameSize % 8 = 0` conjunct). -/
def fnOk (fd : FunDef) : Bool :=
  fd.argc ≤ 8 && fd.rvc ≤ 8 && totalFrame fd ≤ 2000 && fd.frameSize % 8 == 0

/-- Prologue: drop sp, save ra, park params from a0.., `sd x0` every other
    slot (matches IL register-file zeroing EXACTLY), materialize the user-frame
    base into frameReg's slot, then zero the user frame `[sp+userOff, sp+totalFrame)`
    word-by-word (matches IL `frameEnter`'s `zeroRange` — the machine half of the
    zero-init decision; a callee reads 0, not a returned sibling's stale slots). -/
def prologue (fd : FunDef) : List SymInstr :=
  let tf := totalFrame fd
  let params := fd.params.toList
  [.ins (.addi SP SP (BitVec.ofInt 12 (-(tf : Int)))),
   .ins (.sd SP RA 0)]
  ++ params.zipIdx.flatMap (fun pi => storeSlot pi.1 (A pi.2))
  ++ ((List.range (maxRegF fd + 1)).filter
        (fun r => r != 0 && !params.contains r && r != fd.frameReg)).map
       (fun r => .ins (.sd SP 0 (BitVec.ofNat 12 (slotOff r))))
  ++ (if fd.frameReg = 0 then [] else
        [.ins (.addi T0 SP (BitVec.ofNat 12 (userOff fd)))] ++ storeSlot fd.frameReg T0)
  ++ (List.range (fd.frameSize / 8)).map
       (fun i => .ins (.sd SP 0 (BitVec.ofNat 12 (userOff fd + 8 * i))))

/-- Epilogue (jumped to by `ret`, fallen into on `normal`): rets → a0..,
    restore ra + sp, return. -/
def epilogue (fd : FunDef) : List SymInstr :=
  fd.rets.toList.zipIdx.flatMap (fun ri => loadSlot ri.1 (A ri.2))
  ++ [.ins (.ld RA SP 0),
      .ins (.addi SP SP (BitVec.ofNat 12 (totalFrame fd))),
      .ins (.jalr 0 RA 0)]

/-- Compile one function to a symbolic stream. -/
def compileFun (dat : Data) (fd : FunDef) : M (List SymInstr) := do
  let epi ← fresh
  let body ← lower dat [] [] epi fd.body
  pure <| prologue fd ++ body ++ [.label epi] ++ epilogue fd

/-! ### Layout & resolution -/

/-- Emitted size of a symbolic instruction (fixed per constructor — layout
    must be value-independent). `cref` = jal-pc-read + 3-instr delta synth +
    add (see `resolveOne`). -/
def symSize : SymInstr → Nat
  | .label _ => 0
  | .cref _  => 20
  | _        => 4

/-- Pass A over one stream from byte position `pos`: positioned items,
    label→addr entries, next position. -/
def layoutItems : List SymInstr → Nat → List (Nat × SymInstr) × List (Nat × Nat) × Nat
  | [], pos => ([], [], pos)
  | .label l :: rest, pos =>
      let (flat, lbls, pos') := layoutItems rest pos
      ((pos, .label l) :: flat, (l, pos) :: lbls, pos')
  | si :: rest, pos =>
      let (flat, lbls, pos') := layoutItems rest (pos + symSize si)
      ((pos, si) :: flat, lbls, pos')

/-- Pass A: walk the whole program, assigning byte positions. Returns the flat
    positioned stream, the label→addr map, the function→addr map, and the end
    position (total code bytes). -/
def layout : List (Name × List SymInstr) →
    (start : Nat) →
    List (Nat × SymInstr) × List (Nat × Nat) × List (Name × Nat) × Nat
  | [], pos => ([], [], [], pos)
  | (n, items) :: rest, pos =>
      let (flat1, lbls1, pos') := layoutItems items pos
      let (flat2, lbls2, fns, endP) := layout rest pos'
      (flat1 ++ flat2, lbls1 ++ lbls2, (n, pos) :: fns, endP)

/-- Resolve one positioned symbolic instruction (range-checked). `cref d`:
    `jal T0, +4` reads the pc (T0 := address of the next instruction — pc-read
    with NO auipc, staying inside the 16-encoding surface and keeping the blob
    position-independent), then a fixed 3-instr synth of the delta to the data
    object into T1, then `add T0, T0, T1`. -/
def resolveOne (lbls : List (Nat × Nat)) (fns : List (Name × Nat))
    (dats : List (Name × Nat)) :
    Nat × SymInstr → Option (List Instr)
  | (_,   .label _)      => some []
  | (_,   .ins i)        => some [i]
  | (pos, .cref d)       => do
      let off ← List.lookup d dats
      let δ : Int := (off : Int) - ((pos : Int) + 4)
      let lo : Int := ((δ + 2048) % 4096) - 2048
      let hi : Int := (δ - lo) / 4096
      if -2048 ≤ hi && hi ≤ 2047 then
        some [.jal T0 (BitVec.ofInt 21 4),
              .addi T1 0 (BitVec.ofInt 12 hi), .slli T1 T1 12,
              .addi T1 T1 (BitVec.ofInt 12 lo),
              .add T0 T0 T1]
      else none
  | (pos, .br c a b l)   => do
      let tgt ← List.lookup l lbls
      let δ : Int := (tgt : Int) - (pos : Int)
      if -4096 ≤ δ && δ ≤ 4094 then some [condInstr c a b δ] else none
  | (pos, .jmp l)        => do
      let tgt ← List.lookup l lbls
      let δ : Int := (tgt : Int) - (pos : Int)
      if -(2^20 : Int) ≤ δ && δ ≤ (2^20 : Int) - 2 then some [jal0 δ] else none
  | (pos, .callf f)      => do
      let tgt ← List.lookup f fns
      let δ : Int := (tgt : Int) - (pos : Int)
      if -(2^20 : Int) ≤ δ && δ ≤ (2^20 : Int) - 2
      then some [.jal RA (BitVec.ofInt 21 δ)] else none

def pad8 (n : Nat) : Nat := (n + 7) / 8 * 8

/-- Byte offsets of the data objects, laid out 8-aligned from `start`
    (mirrors `Prog.layoutData`'s spacing). -/
def dataOffsets (start : Nat) : Data → List (Name × Nat)
  | [] => []
  | (n, bs) :: rest => (n, start) :: dataOffsets (start + pad8 bs.length) rest

/-- The data segment bytes, each object zero-padded to 8. -/
def dataBytes : Data → List Byte
  | [] => []
  | (_, bs) :: rest =>
      bs ++ List.replicate (pad8 bs.length - bs.length) 0 ++ dataBytes rest

/-- Compile a whole program. The stream is `jal ra, entry` (the 4-byte stub at
    offset 0), a `jal x0, 0` self-loop landing pad at offset 4 — the HALT
    address, occupied by a real instruction so no function entry can collide
    with it — then every function in env order, then (in `progBytes`) the
    data segment. Run the result with `runFuel (codeBase+4)`. `none` =
    ill-formed program, per-function limits exceeded, missing entry, data too
    large, or a branch/jump/cref out of range. The `T` variant also returns
    the function and data byte-offset tables. -/
def compileProgT (P : Program) (entry : Name) :
    Option (List Instr × List (Name × Nat) × List (Name × Nat)) :=
  if !(wfProgram P && P.env.all (fun nf => fnOk nf.2)
       && (List.lookup entry P.env).isSome
       && P.data.all (fun d => d.2.length < 2 ^ 22))    -- cref/clen synth range
       -- NOTE: bound tightened 2^23 → 2^22 (2026-07-05). `clen` synthesizes the
       -- data length via `synthConst` (no range check), whose hi immediate is
       -- `synthHi len = ⌊(len+2048)/4096⌋`; that hits 2048 for `len ∈ [2^23−2048,
       -- 2^23)`, overflowing `BitVec.ofInt 12` (wraps to −2048 ⇒ wrong length).
       -- 2^22 sits well inside the synthesizable band; discharges ProgSim `hdat`.
  then none
  else
    let segs : List (Name × List SymInstr) :=
      (P.env.mapM (fun nf => do pure (nf.1, ← compileFun P.data nf.2)) : M _).run' 0
    let (flat, lbls, fns, codeEnd) :=
      layout (("", [.callf entry, .ins (jal0 0)]) :: segs) 0
    -- SAME layout function as the IL harness (`Prog.dbaseOf`/`installData`
    -- use `dataOffsetsFrom 0`); correspondence proved in `Prog.dataSegment_at`.
    let dats := dataOffsetsFrom (pad8 codeEnd) P.data
    ((flat.mapM (resolveOne lbls fns dats)).map List.flatten).map
      (fun is => (is, fns.filter (fun f => f.1 != ""), dats))

def compileProg (P : Program) (entry : Name) : Option (List Instr) :=
  (compileProgT P entry).map (·.1)

/-- The full loadable blob: code, zero pad to 8, then the data segment
    (offsets per `dataOffsets`). This — not `compileProg`'s instruction list
    alone — is what runs when the program has data. -/
def progBytes (P : Program) (entry : Name) : Option (List Byte) :=
  (compileProg P entry).map fun is =>
    let code := LowIR.asmBytes is
    code ++ List.replicate (pad8 code.length - code.length) 0 ++ dataSegment P.data

end LowIR.Compile
