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
open LowIR.Prog (Reg Name FunDef Env wfEnv)
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

/-- Lower one statement. `brks`/`conts` are the enclosing block-end / loop-top
    label stacks (indexed exactly like `brkB`/`contL`'s de Bruijn indices);
    `epi` is this function's epilogue label. `wf` guarantees index ranges and
    call arities; out-of-range lookups fall back to label 0 (never emitted for
    a wf program). -/
def lower (brks conts : List Nat) (epi : Nat) : PStmt → M (List SymInstr)
  | .skip           => pure []
  | .annot _        => pure []
  | .seq a b        => do pure ((← lower brks conts epi a) ++ (← lower brks conts epi b))
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
      let et ← lower brks conts epi t
      let ee ← lower brks conts epi e
      pure <| loadSlot a T0 ++ loadSlot b T1
           ++ [.br c T0 T1 lT] ++ ee ++ [.jmp lEnd, .label lT] ++ et ++ [.label lEnd]
  | .while c a b body => do
      let lTop ← fresh; let lBody ← fresh; let lEnd ← fresh
      let eb ← lower brks (lTop :: conts) epi body
      pure <| [.label lTop] ++ loadSlot a T0 ++ loadSlot b T1
           ++ [.br c T0 T1 lBody, .jmp lEnd, .label lBody]
           ++ eb ++ [.jmp lTop, .label lEnd]
  | .block body     => do
      let lEnd ← fresh
      let eb ← lower (lEnd :: brks) conts epi body
      pure <| eb ++ [.label lEnd]
  | .brkB k         => pure [.jmp (brks.getD k 0)]
  | .contL k        => pure [.jmp (conts.getD k 0)]
  | .ret            => pure [.jmp epi]
  | .call _ _ f args rets => do
      let loads  := args.toList.zipIdx.flatMap fun ri => loadSlot ri.1 (A ri.2)
      let stores := rets.toList.zipIdx.flatMap fun ri => storeSlot ri.1 (A ri.2)
      pure <| loads ++ [.callf f] ++ stores

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
    and all slot offsets / frame adjustments within imm12. -/
def fnOk (fd : FunDef) : Bool :=
  fd.argc ≤ 8 && fd.rvc ≤ 8 && totalFrame fd ≤ 2000

/-- Prologue: drop sp, save ra, park params from a0.., `sd x0` every other
    slot (matches IL zero-init EXACTLY), materialize the user-frame base into
    frameReg's slot. -/
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

/-- Epilogue (jumped to by `ret`, fallen into on `normal`): rets → a0..,
    restore ra + sp, return. -/
def epilogue (fd : FunDef) : List SymInstr :=
  fd.rets.toList.zipIdx.flatMap (fun ri => loadSlot ri.1 (A ri.2))
  ++ [.ins (.ld RA SP 0),
      .ins (.addi SP SP (BitVec.ofNat 12 (totalFrame fd))),
      .ins (.jalr 0 RA 0)]

/-- Compile one function to a symbolic stream. -/
def compileFun (fd : FunDef) : M (List SymInstr) := do
  let epi ← fresh
  let body ← lower [] [] epi fd.body
  pure <| prologue fd ++ body ++ [.label epi] ++ epilogue fd

/-! ### Layout & resolution -/

/-- Pass A over one stream from byte position `pos`: positioned items,
    label→addr entries, next position. Labels occupy 0 bytes, all else 4. -/
def layoutItems : List SymInstr → Nat → List (Nat × SymInstr) × List (Nat × Nat) × Nat
  | [], pos => ([], [], pos)
  | .label l :: rest, pos =>
      let (flat, lbls, pos') := layoutItems rest pos
      ((pos, .label l) :: flat, (l, pos) :: lbls, pos')
  | si :: rest, pos =>
      let (flat, lbls, pos') := layoutItems rest (pos + 4)
      ((pos, si) :: flat, lbls, pos')

/-- Pass A: walk the whole program, assigning byte positions. Returns the flat
    positioned stream, the label→addr map, and the function→addr map. -/
def layout : List (Name × List SymInstr) →
    (start : Nat) → List (Nat × SymInstr) × List (Nat × Nat) × List (Name × Nat)
  | [], _ => ([], [], [])
  | (n, items) :: rest, pos =>
      let (flat1, lbls1, pos') := layoutItems items pos
      let (flat2, lbls2, fns) := layout rest pos'
      (flat1 ++ flat2, lbls1 ++ lbls2, (n, pos) :: fns)

/-- Resolve one positioned symbolic instruction (range-checked). -/
def resolveOne (lbls : List (Nat × Nat)) (fns : List (Name × Nat)) :
    Nat × SymInstr → Option (List Instr)
  | (_,   .label _)      => some []
  | (_,   .ins i)        => some [i]
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

/-- Compile a whole program. The stream is `jal ra, entry` (the 4-byte stub at
    offset 0), a `jal x0, 0` self-loop landing pad at offset 4 — the HALT
    address, occupied by a real instruction so no function entry can collide
    with it — then every function in env order. Run the result with
    `runFuel (codeBase+4)`. `none` = ill-formed env, per-function limits
    exceeded, missing entry, or a branch/jump out of range. The `T` variant
    also returns the function→byte-offset table (e.g. for an external shim
    that calls a function inside the blob directly). -/
def compileProgT (env : Env) (entry : Name) :
    Option (List Instr × List (Name × Nat)) :=
  if !(wfEnv env && env.all (fun nf => fnOk nf.2) && (List.lookup entry env).isSome)
  then none
  else
    let segs : List (Name × List SymInstr) :=
      (env.mapM (fun nf => do pure (nf.1, ← compileFun nf.2)) : M _).run' 0
    let (flat, lbls, fns) := layout (("", [.callf entry, .ins (jal0 0)]) :: segs) 0
    ((flat.mapM (resolveOne lbls fns)).map List.flatten).map
      (fun is => (is, fns.filter (fun f => f.1 != "")))

def compileProg (env : Env) (entry : Name) : Option (List Instr) :=
  (compileProgT env entry).map (·.1)

/-- Program bytes (little-endian), ready to load at a code base. -/
def progBytes (env : Env) (entry : Name) : Option (List Byte) :=
  (compileProg env entry).map LowIR.asmBytes

end LowIR.Compile
