-- syntax and semantics: top-level functions + tuples + exceptions

abbrev Var := String

inductive Expr where
  | int (i : Int) : Expr
  | succ (e : Expr) : Expr
  | pred (e : Expr) : Expr
  | plus (e1 : Expr) (e2 : Expr) : Expr
  | times (e1 : Expr) (e3 : Expr) : Expr
  | ifte (e1 e2 e3 : Expr) : Expr
  | bool (b : Bool) : Expr
  | neg (e : Expr) : Expr
  | bind (x : Var) (e1 e2 : Expr) : Expr
  | var (x : Var) : Expr
  | call (f : Var) (e : Expr) : Expr
  | pair (e1 e2 : Expr) : Expr
  | fst (e : Expr) : Expr
  | snd (e : Expr) : Expr
  | throw (e : Expr) : Expr
  | handle (e : Expr) (f : Var) : Expr
  | vec (es : List Expr) : Expr
  | vget (e : Expr) (i : Nat) : Expr
  | vset (e : Expr) (i : Nat) (v : Expr) : Expr

inductive Defn where
  | defn (f x : Var) (e : Expr)

inductive Val where
  | int (i : Int) : Val
  | bool (b : Bool) : Val
  | pair (v1 v2 : Val)
  | vec (vs : List Val)

inductive Ans where
  | val (v : Val) : Ans
  | exn (v : Val) : Ans

abbrev Env := List (Var × Val)

abbrev Defns := List Defn

abbrev Prog := Defns × Expr

def Env.lookup (r : Env) (x : Var) : Option Val :=
  match r with
  | [] => none
  | (y,v) :: r =>
    if x = y then some v else Env.lookup r x

def Defns.lookup (ds : Defns) (f : Var) : Option Defn :=
  match ds with
  | [] => none
  | ((.defn g y e) :: ds) =>
    if f = g then some (.defn g y e) else Defns.lookup ds f

inductive Eval : Defns → Env → Expr → Ans → Prop where
  | intr {ds r} (i : Int) :
    Eval ds r (.int i) (.val (.int i))
  | boolr {ds r} (b : Bool) :
    Eval ds r (.bool b) (.val (.bool b))
  | succr {ds r e i} :
    Eval ds r e (.val (.int i)) →
    Eval ds r (.succ e) (.val (.int (i + 1)))
  | succ_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.succ e) (.exn v)
  | predr {ds r e i} :
    Eval ds r e (.val (.int i)) →
    Eval ds r (.pred e) (.val (.int (i - 1)))
  | pred_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.pred e) (.exn v)
  | plusr {ds r e1 i1 e2 i2} :
    Eval ds r e1 (.val (.int i1)) →
    Eval ds r e2 (.val (.int i2)) →
    Eval ds r (.plus e1 e2) (.val (.int (i1 + i2)))
  | plus_proplr {ds r e1 v e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.plus e1 e2) (.exn v)
  | plus_proprr {ds r e1 e2 v1 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.exn v2) →
    Eval ds r (.plus e1 e2) (.exn v2)
  | timesr {ds r e1 i1 e2 i2} :
    Eval ds r e1 (.val (.int i1)) →
    Eval ds r e2 (.val (.int i2)) →
    Eval ds r (.times e1 e2) (.val (.int (i1 * i2)))
  | times_proplr {ds r e1 v e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.times e1 e2) (.exn v)
  | times_proprr {ds r e1 e2 v1 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.exn v2) →
    Eval ds r (.times e1 e2) (.exn v2)
  | iftr {ds r e1 e2 a e3} :
    Eval ds r e1 (.val (.bool true)) →
    Eval ds r e2 a →
    Eval ds r (.ifte e1 e2 e3) a
  | iffr {ds r e1 e3 a e2} :
    Eval ds r e1 (.val (.bool false)) →
    Eval ds r e3 a →
    Eval ds r (.ifte e1 e2 e3) a
  | if_propr {ds r e1 v e2 e3} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.ifte e1 e2 e3) (.exn v)
  | negtr {ds r e} :
    Eval ds r e (.val (.bool true)) →
    Eval ds r (.neg e) (.val (.bool false))
  | negfr {ds r e} :
    Eval ds r e (.val (.bool false)) →
    Eval ds r (.neg e) (.val (.bool true))
  | neg_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.neg e) (.exn v)
  | varr {ds r v x} :
    Env.lookup r x = some v →
    Eval ds r (.var x) (.val v)
  | bindr {ds r e1 v1 x a e2} :
    Eval ds r e1 (.val v1) →
    Eval ds ((x, v1) :: r) e2 a →
    Eval ds r (.bind x e1 e2) a
  | bind_propr {ds r e1 v x e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.bind x e1 e2) (.exn v)
  | callr {ds r e v1 f x e' a} :
    Eval ds r e (.val v1) →
    Defns.lookup ds f = some (.defn f x e') →
    Eval ds [(x,v1)] e' a →
    Eval ds r (.call f e) a
  | call_propr {ds r e f v} :
    Eval ds r e (.exn v) →
    Eval ds r (.call f e) (.exn v)
  | pairr {ds r e1 v1 e2 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.val v2) →
    Eval ds r (.pair e1 e2) (.val (.pair v1 v2))
  | pair_proplr {ds r e1 v e2} :
    Eval ds r e1 (.exn v) →
    Eval ds r (.pair e1 e2) (.exn v)
  | pair_proprr {ds r e1 e2 v1 v2} :
    Eval ds r e1 (.val v1) →
    Eval ds r e2 (.exn v2) →
    Eval ds r (.pair e1 e2) (.exn v2)
  | fstr {ds r e v1 v2} :
    Eval ds r e (.val (.pair v1 v2)) →
    Eval ds r (.fst e) (.val v1)
  | fst_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.fst e) (.exn v)
  | sndr {ds r e v1 v2} :
    Eval ds r e (.val (.pair v1 v2)) →
    Eval ds r (.snd e) (.val v2)
  | snd_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.snd e) (.exn v)
  | throwr {ds r e v} :
    Eval ds r e (.val v) →
    Eval ds r (.throw e) (.exn v)
  | throw_propr {ds r e v} :
    Eval ds r e (.exn v) →
    Eval ds r (.throw e) (.exn v)
  | handle_valr {ds r e v f} :
    Eval ds r e (.val v) →
    Eval ds r (.handle e f) (.val v)
  | handle_exnr {ds r e v f x e' a} :
    Eval ds r e (.exn v) →
    Defns.lookup ds f = some (.defn f x e') →
    Eval ds [(x,v)] e' a →
    Eval ds r (.handle e f) a
    | vec_nilr {ds r} :
    Eval ds r (.vec []) (.val (.vec []))
  | vec_consr {ds r e es v vs} :
    Eval ds r e (.val v) →
    Eval ds r (.vec es) (.val (.vec vs)) →
    Eval ds r (.vec (e :: es)) (.val (.vec (v :: vs)))
  | vec_proplr {ds r e es v} :
    Eval ds r e (.exn v) →
    Eval ds r (.vec (e :: es)) (.exn v)
  | vec_proprr {ds r e es v v'} :
    Eval ds r e (.val v) →
    Eval ds r (.vec es) (.exn v') →
    Eval ds r (.vec (e :: es)) (.exn v')
  | vgetr {ds r e i vs v} :
    Eval ds r e (.val (.vec vs)) →
    vs[i]? = some v →
    Eval ds r (.vget e i) (.val v)
  | vget_propr {ds r e i v} :
    Eval ds r e (.exn v) →
    Eval ds r (.vget e i) (.exn v)
  | vsetr {ds r e i e_v vs v v_old} :
    Eval ds r e (.val (.vec vs)) →
    Eval ds r e_v (.val v) →
    vs[i]? = some v_old →
    Eval ds r (.vset e i e_v) (.val (.vec (vs.set i v)))
  | vset_proplr {ds r e i e_v v} :
    Eval ds r e (.exn v) →
    Eval ds r (.vset e i e_v) (.exn v)
  | vset_proprr {ds r e i e_v vs v} :
    Eval ds r e (.val (.vec vs)) →
    Eval ds r e_v (.exn v) →
    Eval ds r (.vset e i e_v) (.exn v)


-- A little stack machine semantics

inductive Op where
| plus | times | flip

inductive Instr where
| push (i : Int) : Instr
| op (o : Op) : Instr
| branch (is1 is2 : List Instr)
| get (n : Nat) : Instr
| pop : Instr
| exch : Instr
| call : Instr
| dup : Instr
| alloc (n : Nat) : Instr
| read (o : Int) : Instr
| write (o : Int) : Instr
| trycatch (is1 is2 : List Instr) : Instr
| abort : Instr

abbrev Instrs := List Instr

abbrev Stack := List Int

abbrev IDefns := List Instrs

inductive OpEval : Op → List Int → Int → Prop where
| flip0 : OpEval .flip [0] 1
| flip1 : OpEval .flip [1] 0
| plus {i j} : OpEval .plus [j, i] (i+j)
| mult {i j} : OpEval .times [j, i] (i*j)

abbrev Heap := List (Int × Int)

def Heap.lookup (h : Heap) (i : Int) : Option Int :=
  match h with
  | [] => none
  | (j,k) :: h =>
    if i = j then some k else Heap.lookup h i

def Heap.ext (h : Heap) (i j : Int) : Heap :=
  (i, j) :: h

def FreshBlock (h : Heap) (base : Int) (n : Nat) : Prop :=
  ∀ k : Nat, k < n → Heap.lookup h (base + Int.ofNat k) = none

inductive Frame where
  | ret (is : Instrs)
  | handler (handler : Instrs) (k : Instrs) (s : Stack)

inductive Step : IDefns →
                 Instrs → List Frame → Stack → Heap →
                 Instrs → List Frame → Stack → Heap → Prop where
| pushr {ds v is cs s h} :
  Step ds (.push v :: is) cs s h is cs (v :: s) h
| opr {ds o vs v is cs s h} : OpEval o vs v →
  Step ds (.op o :: is) cs (vs ++ s) h is cs (v :: s) h
| branchtr {ds is1 is2 is cs s h} :
  Step ds (.branch is1 is2 :: is) cs (1 :: s) h (is1 ++ is) cs s h
| branchfr {ds is1 is2 is cs s h} :
  Step ds (.branch is1 is2 :: is) cs (0 :: s) h (is2 ++ is) cs s h
| popr {ds is cs i s h} :
  Step ds (.pop :: is) cs (i :: s) h is cs s h
| getr {ds n is cs s h i} :
  s[n]? = some i →
  Step ds (.get n :: is) cs s h is cs (i :: s) h
| exchr {ds is cs v1 v2 s h} :
  Step ds (.exch :: is) cs (v1 :: v2 :: s) h is cs (v2 :: v1 :: s) h
| callr {ds i is' is cs s h} :
  ds[i.toNat]? = some is' →
  Step ds (.call :: is) cs (i :: s) h (is' ++ is) cs s h
| dupr {ds is cs i s h} :
  Step ds (.dup :: is) cs (i :: s) h is cs (i :: i :: s) h
| allocr {ds is cs s h n i} :
  FreshBlock h i n →
  Step ds (.alloc n :: is) cs s h is cs (i :: s) h
| readr {ds h i j o is cs s} :
  Heap.lookup h (i + o) = some j →
  Step ds (.read o :: is) cs (i :: s) h is cs (j :: s) h
| writer {ds is cs i j o s h} :
  Step ds (.write o :: is) cs (i :: j :: s) h is cs (i :: s) (Heap.ext h (i + o) j)
| trycatchr {ds is body handle cs s h} :
  Step ds (.trycatch body handle :: is) cs s h
    body (.handler handle is s :: cs) s h
| ret_handler {ds handle k og_stack cs s h} :
  Step ds [] (.handler handle k og_stack :: cs) s h k cs s h
| abort_handler {ds is' handle k og_stack cs h i} :
    Step ds (.abort :: is') (.handler handle k og_stack :: cs) (i :: _) h handle (.ret k :: cs) (i :: og_stack) h
| abort_retr {ds is' k cs s h} :
  Step ds (.abort :: is') (.ret k :: cs) s h (.abort :: is') cs s h
| retr {ds is cs s h} :
  Step ds [] (.ret is :: cs) s h is cs s h

inductive Steps : IDefns →
  Instrs → List Frame → Stack → Heap →
  Instrs → List Frame → Stack → Heap → Prop where
| refl {ds s is cs h} : Steps ds is cs s h is cs s h
| trans {ds is cs s h is1 cs1 s1 h1 is' cs' s' h'} :
  Steps ds is cs s h is1 cs1 s1 h1 ->
  Step ds is1 cs1 s1 h1 is' cs' s' h' ->
  Steps ds is cs s h is' cs' s' h'


-- compiler

abbrev CEnv := List (Option Var)

def CEnv.lookup (c : CEnv) (x : Var) : Option Nat :=
  match c with
  | [] => none
  | some y :: c =>
    if x = y then some 0 else
      (CEnv.lookup c x).map .succ
  | none :: c =>
      (CEnv.lookup c x).map .succ

def Defns.indexOf (ds : Defns) (f : Var) : Option Nat :=
  match ds with
  | [] => none
  | (.defn g _ _) :: ds =>
    if f = g then some 0 else (indexOf ds f).map .succ

mutual
  def compile (ds : Defns) (c : CEnv) (e : Expr) : List Instr :=
    match e with
    | .int i => [.push i]
    | .bool b => [.push (if b then 1 else 0)]
    | .succ e =>
      compile ds c e ++
      [.push 1, .op .plus]
    | .pred e =>
      compile ds c e ++
      [.push (-1), .op .plus]
    | .neg e =>
      compile ds c e ++
      [.op .flip]
    | .plus e1 e2 =>
      compile ds c e1 ++
      compile ds (none :: c) e2 ++
      [.op .plus]
    | .times e1 e2 =>
      compile ds c e1 ++
      compile ds (none :: c) e2 ++
      [.op .times]
    | .ifte e1 e2 e3 =>
      compile ds c e1 ++
      [.branch (compile ds c e2) (compile ds c e3)]
    | .var x =>
      match CEnv.lookup c x with
      | some n =>
        [.get n]
      | none => [] -- whatever
    | .bind x e1 e2 =>
      compile ds c e1 ++
      compile ds (some x :: c) e2 ++
      [.exch, .pop]
    | .call f e =>
      compile ds c e ++
      match Defns.indexOf ds f with
      | some n => [.push (Int.ofNat n), .call, .exch, .pop]
      | none => [] -- whatever
    | .pair e1 e2 =>
      compile ds c e1 ++
      compile ds (none :: c) e2 ++
      [.alloc 2, .write 1, .write 0]
    | .fst e =>
      compile ds c e ++
      [.read 0]
    | .snd e =>
      compile ds c e ++
      [.read 1]
    | .throw e =>
      compile ds c e ++
      [.abort]
    | .handle e f =>
      [.trycatch (compile ds c e)
        (match Defns.indexOf ds f with
        | some n => [.push (Int.ofNat n), .call, .exch, .pop]
        | none   => [])]
    | .vec es =>
      [.alloc es.length] ++ build_vec 0 es ds c
    | .vget e i =>
      compile ds c e ++
      [.read (Int.ofNat i)]
    | .vset e i v =>
      compile ds c e ++
      compile ds (none :: c) v ++
      [.exch, .write (Int.ofNat i)]

def build_vec (i : Nat) (es' : List Expr) (ds : Defns) (c : CEnv) : List Instr :=
  match es' with
  | [] => []
  | e' :: rest =>
    compile ds (none :: c) e' ++
    -- swap the stack to be pointer, value so write uses the vec pointer
    -- writes value in stackto i offset from pointer
    [.exch, .write (Int.ofNat i)] ++
    build_vec (i + 1) rest ds c

end

def compile_defn (ds : Defns) (d : Defn) :=
  match d with
  | .defn _ x e => compile ds [some x] e

def compile_defns (ds : Defns) :=
  ds.map (compile_defn ds)

-- proof

inductive Represents : Val -> Int -> Heap -> Prop where
  | int {i h} : Represents (.int i) i h
  | bool {b h} : Represents (.bool b) (if b then 1 else 0) h
  | pair {v1 i1 h v2 i2 i} :
    Represents v1 i1 h ->
    Represents v2 i2 h ->
    Heap.lookup h (i+0) = some i1 ->
    Heap.lookup h (i+1) = some i2 ->
    Represents (.pair v1 v2) i h
  | vec {vs ptr h} (ivs : Nat → Int) :
      -- `ivs` is a function that maps an index `k` to its physical Int representation.
      (∀ k v, vs[k]? = some v → Represents v (ivs k) h) →
      (∀ k v, vs[k]? = some v → Heap.lookup h (ptr + Int.ofNat k) = some (ivs k)) →
      Represents (.vec vs) ptr h

inductive Related : Stack -> CEnv -> Env -> Heap -> Prop where
  | mt {s h} : Related s [] [] h
  | push {s c r i h} :
    Related s c r h ->
    Related (i :: s) (none :: c) r h
  | bind {s c r x v h i} :
    Related s c r h ->
    Represents v i h ->
    Related (i :: s) ((some x) :: c) ((x,v) :: r) h

def AnsRep : Ans → Int → Heap → Prop
  | .val v, i, h => Represents v i h
  | .exn v, i, h => Represents v i h

-- * values return normally;
-- * exceptions skip .ret frames;
-- * exceptions jump to the nearest .handler;
-- * if there is no handler, they leave the machine at (.abort :: is).

-- the thing from piazza
inductive ExnContinuesWith :
  Instrs → List Frame →
  Int → Instrs → List Frame → Stack → Prop where
  | exn_nil {is i is'} (s : Stack) :
    ExnContinuesWith is [] i (.abort :: is') [] s
  | exn_ret {is k cs i is' cs' og_stack} :
    ExnContinuesWith is cs i is' cs' og_stack →
    ExnContinuesWith is (.ret k :: cs) i is' cs' og_stack
  | exn_handler {is handle k cs i og_stack} :
    ExnContinuesWith is (.handler handle k og_stack :: cs) i
      handle (.ret k :: cs) (i :: og_stack)

inductive ContinuesWith :
  Ans → Instrs → List Frame → Stack →
  Int → Instrs → List Frame → Stack → Prop where
  | val {v is cs s i} :
    ContinuesWith (.val v) is cs s i
      is cs (i :: s)
  | exn {v is cs s i is' cs' og_stack} :
    ExnContinuesWith is cs i is' cs' og_stack →
    ContinuesWith (.exn v) is cs s i is' cs' og_stack

def HeapExtends (h h' : Heap) : Prop :=
  ∀ a v,
  Heap.lookup h a = some v ->
  Heap.lookup h' a = some v

-- lemma about heap stability
theorem Represents.mono {v i h h'} :
  Represents v i h ->
  HeapExtends h h' ->
  Represents v i h' := by
  intro hrep hext
  induction hrep with
  | int => constructor
  | bool => constructor
  | pair hv1 hv2 hlook0 hlook1 ih1 ih2 =>
    apply Represents.pair (ih1 hext) (ih2 hext)
    · exact hext _ _ hlook0
    · exact hext _ _ hlook1
  | vec ivs hrep_vs hlook_vs ih =>
    apply Represents.vec ivs
    · intro k v hk
      exact ih k v hk hext
    · intro k v hk

      exact hext _ _ (hlook_vs k v hk)

-- lemma about state stability across env/stack and heap
theorem Related.mono {s c r h h'} :
  Related s c r h ->
  HeapExtends h h' ->
  Related s c r h' := by
  intro hrel hext
  induction hrel with
  | mt => exact .mt
  | push hrel ih =>
    exact .push (ih hext)
  | bind hrel hrep ih =>
    exact .bind (ih hext) (Represents.mono hrep hext)

-- this lemma states the rest of the instructions don't
-- matter if we are propagating an exception since control
-- flow is yielded to the exception
theorem exn_lemma
  {v is1 is2 cs s i is' cs' s'} :
  ContinuesWith (.exn v) is1 cs s i is' cs' s' →
  ContinuesWith (.exn v) is2 cs s i is' cs' s' := by
  intro h
  cases h with
  | exn h' =>
    apply ContinuesWith.exn
    induction h' with
    | exn_nil s =>
      apply ExnContinuesWith.exn_nil
    | exn_ret ih =>
      apply ExnContinuesWith.exn_ret
      assumption
    | exn_handler =>
      apply ExnContinuesWith.exn_handler

-- transitivitiy between sequences of steps
theorem Steps.trans_steps {ds is1 cs1 s1 h1 is2 cs2 s2 h2 is3 cs3 s3 h3} :
  Steps ds is1 cs1 s1 h1 is2 cs2 s2 h2 →
  Steps ds is2 cs2 s2 h2 is3 cs3 s3 h3 →
  Steps ds is1 cs1 s1 h1 is3 cs3 s3 h3 := by
  intro h12 h23
  induction h23 with
  | refl => assumption
  | trans _ step ih =>
      apply Steps.trans (ih h12) step

theorem abort_exists_steps
  {ds is cs i s h} :
  ∃ is' cs' s',
    Steps ds (.abort :: is) cs (i :: s) h is' cs' s' h ∧
    ExnContinuesWith is cs i is' cs' s' := by
  induction cs generalizing is i s with
  | nil =>
      refine ⟨.abort :: is, [], i :: s, ?_, ?_⟩
      · apply Steps.refl
      · apply ExnContinuesWith.exn_nil
  | cons fr cs ih =>
      cases fr with
      | ret k =>
          obtain ⟨is', cs', s', steps_tail, exn_tail⟩ :=
            ih (is := is) (i := i) (s := s)
          refine ⟨is', cs', s', ?_, ?_⟩
          · apply Steps.trans_steps
            · apply Steps.trans Steps.refl
              apply Step.abort_retr
            · assumption
          · apply ExnContinuesWith.exn_ret
            assumption
      | handler handle k og_stack =>
          refine ⟨handle, .ret k :: cs, i :: og_stack, ?_, ?_⟩
          · apply Steps.trans Steps.refl
            apply Step.abort_handler
          · apply ExnContinuesWith.exn_handler
def maxAbsIntList (xs : List Int) : Nat :=
  xs.foldl (fun m x => Nat.max m (Int.natAbs x)) 0

def dom (h : Heap) : List Int := h.map Prod.fst

theorem le_foldl_maxAbs (acc : Nat) (xs : List Int) :
  acc ≤ xs.foldl (fun m x => Nat.max m (Int.natAbs x)) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.foldl]
      exact Nat.le_trans
        (Nat.le_max_left acc (Int.natAbs x))
        (ih (Nat.max acc (Int.natAbs x)))

theorem natAbs_le_maxAbsIntList_of_mem {a : Int} {xs : List Int} :
  a ∈ xs -> Int.natAbs a ≤ maxAbsIntList xs := by
  intro hmem
  have aux :
    ∀ (ys : List Int) (acc : Nat),
      a ∈ ys ->
      Int.natAbs a ≤ ys.foldl (fun m x => Nat.max m (Int.natAbs x)) acc := by
    intro ys
    induction ys with
    | nil =>
        intro acc hmem
        cases hmem
    | cons x xs ih =>
        intro acc hmem
        simp [List.foldl]
        simp at hmem
        rcases hmem with hhead | htail
        · subst hhead
          exact Nat.le_trans
            (Nat.le_max_right acc (Int.natAbs a))
            (le_foldl_maxAbs (acc := Nat.max acc (Int.natAbs a)) (xs := xs))
        · exact ih (Nat.max acc (Int.natAbs x)) htail
  simpa [maxAbsIntList] using aux xs 0 hmem

theorem lookup_some_mem_dom {h : Heap} {a v : Int} :
  Heap.lookup h a = some v -> a ∈ dom h := by
  intro hlook
  induction h with
  | nil =>
      simp [Heap.lookup] at hlook
  | cons p h ih =>
      rcases p with ⟨j,k⟩
      by_cases ha : a = j
      · subst ha
        simp [dom]
      · have : Heap.lookup h a = some v := by
          simpa [Heap.lookup, ha] using hlook
        have hm : a ∈ dom h := ih this
        simpa [dom] using List.mem_cons_of_mem j hm

theorem exists_freshBlock (h : Heap) (n : Nat) :
  ∃ a : Int, FreshBlock h a n := by
  let M : Nat := maxAbsIntList (dom h)
  refine ⟨Int.ofNat (M + 1), ?_⟩
  intro k hk
  cases hL : Heap.lookup h (Int.ofNat (M + 1) + Int.ofNat k) with
  | none =>
      rfl
  | some v =>
      have hmem : (Int.ofNat (M + 1) + Int.ofNat k) ∈ dom h :=
        lookup_some_mem_dom (by simpa [hL])
      have hbound : Int.natAbs (Int.ofNat (M + 1) + Int.ofNat k) ≤ M := by
        simpa [M] using natAbs_le_maxAbsIntList_of_mem hmem
      have hadd : Int.ofNat (M + 1) + Int.ofNat k = Int.ofNat (M + 1 + k) := by
        simpa [Nat.add_assoc] using (Int.ofNat_add_ofNat (M + 1) k)
      have hbad : M + 1 + k ≤ M := by
        simpa [hadd] using hbound
      have : False := by
        have : M + 1 ≤ M := Nat.le_trans (Nat.le_add_right (M + 1) k) hbad
        exact Nat.not_succ_le_self M (by simpa [Nat.succ_eq_add_one] using this)
      contradiction

  theorem HeapExtends.trans {h h0 h'} :
    HeapExtends h h0 ->
    HeapExtends h0 h' ->
    HeapExtends h h' := by
    intros h1 h2 i v hl
    apply h2
    apply h1
    assumption

theorem HeapExtends.write {h a v} :
  Heap.lookup h a = none ->
  HeapExtends h (Heap.ext h a v) := by
  intro hl a' v' hl'
  by_cases hEq : a' = a
  · subst hEq
    rw [hl] at hl'
    contradiction
  · simp [Heap.lookup, Heap.ext, hEq]
    assumption

theorem ext_lookup_of_ne {h : Heap} {a b i : Int} (hba : b ≠ a) :
  Heap.lookup (Heap.ext h a i) b = Heap.lookup h b := by
  simp [Heap.lookup, Heap.ext, hba]

theorem HeapExtends.allocPair {h : Heap} {a i1 i2 : Int}
    (hf : FreshBlock h a 2) :
    HeapExtends h ((h.ext (a + 1) i2).ext (a + 0) i1) := by
  have hw1 : HeapExtends h (Heap.ext h (a + 1) i2) :=
    HeapExtends.write (hf 1 (by omega))

  have hnone0 : Heap.lookup (Heap.ext h (a + 1) i2) (a + 0) = none := by
    rw [ext_lookup_of_ne]
    · exact hf 0 (by omega)
    · omega

  have hw2 :
      HeapExtends (Heap.ext h (a + 1) i2)
        ((Heap.ext h (a + 1) i2).ext (a + 0) i1) :=
    HeapExtends.write hnone0

  exact HeapExtends.trans hw1 hw2

theorem Related.lookup {s c r x v h} :
  Related s c r h ->
  Env.lookup r x = some v ->
  ∃ n i,
    CEnv.lookup c x = some n /\
    s[n]? = some i /\
    Represents v i h := by

  intros hrel hlook
  induction hrel with
  | mt => cases hlook
  | push hrel' ih =>
    rcases ih hlook with ⟨n, i, hidx, hstk⟩
    refine ⟨n+1, i, ?_, ?_⟩
    · simp [CEnv.lookup, hidx]
    · simp [hstk]
  | bind hrel' hrep ih =>
    rename_i s i' r y v' h i
    by_cases hxy : x = y
    · subst hxy
      simp [Env.lookup] at hlook
      subst hlook
      refine ⟨0, i, ?_, ?_⟩
      · simp [CEnv.lookup]
      · simpa
    · rename_i r'
      simp [Env.lookup, hxy] at hlook
      rcases ih hlook with ⟨n, j, hidx, hstk⟩
      refine ⟨n+1, j, ?_, ?_⟩
      · simp [CEnv.lookup, hxy, hidx]
      · simp [hstk]

theorem indexOf_exists_of_lookup {ds f x e} :
  Defns.lookup ds f = some (.defn f x e) ->
  ∃ n, Defns.indexOf ds f = some n := by
  intro hlook
  induction ds with
  | nil => cases hlook
  | cons d ds ih =>
    cases d with
    | defn g y e' =>
      by_cases hfg : f = g
      · subst hfg
        simp [Defns.lookup] at hlook
        rcases hlook with ⟨rfl,rfl⟩
        exact ⟨0, by simp [Defns.indexOf]⟩
      · simp [Defns.lookup, hfg] at hlook
        rcases ih hlook with ⟨n, hn⟩
        exact ⟨n+1, by simp [Defns.indexOf, hfg, hn]⟩

theorem lookup_indexOf_get {ds f x e n} :
  Defns.lookup ds f = some (Defn.defn f x e) ->
  Defns.indexOf ds f = some n ->
  ds[n]? = some (.defn f x e) := by
  intros hl hi
  induction ds generalizing n with
  | nil => cases hl
  | cons d ds ih =>
    cases d with
    | defn g y e' =>
      by_cases hfg : f = g
      · subst hfg
        simp [Defns.indexOf] at hi
        simp [Defns.lookup] at hl
        subst hi
        simpa
      · simp [Defns.indexOf,hfg] at hi
        simp [Defns.lookup,hfg] at hl
        rcases hi with ⟨a, hia, rfl⟩
        have := ih hl hia
        simpa

theorem RelatedDefns.lookup {ds f x e} :
  Defns.lookup ds f = some (.defn f x e) ->
  ∃ n, Defns.indexOf ds f = some n ∧
    (compile_defns ds)[n]? = some (compile ds [some x] e) := by
  intro hlook
  rcases indexOf_exists_of_lookup hlook with ⟨n, hidx⟩
  simp [compile_defns]
  refine ⟨n, hidx, ?_⟩
  refine ⟨_, lookup_indexOf_get hlook hidx, ?_⟩
  simp [compile_defn]

set_option maxHeartbeats 0
theorem compiler_correct_general
  {ds c r e a is cs s h} :
  Related s c r h →
  Eval ds r e a →
  ∃ i h' is' cs' s',
    Steps (compile_defns ds) (compile ds c e ++ is) cs s h is' cs' s' h' ∧
    ContinuesWith a is cs s i is' cs' s' ∧
    AnsRep a i h' ∧
    HeapExtends h h' := by
  intros rel eval
  induction eval generalizing is s c h cs with
  | intr x =>
    exists x, h, is, cs, x :: s
    -- steps part of conjunction
    constructor
    · simp [compile]
      apply Steps.trans Steps.refl Step.pushr
    -- continues part of conjunction
    constructor
    · apply ContinuesWith.val
    -- repr part of conjunction
    constructor
    · apply Represents.int
    -- heap part of conjunction
    · intros _ _ h_lookup
      assumption
  | boolr x =>
    -- same idea as above but x witness is bounded
    exists (if x then 1 else 0), h, is, cs, (if x then 1 else 0) :: s
    constructor
    · simp [compile]
      apply Steps.trans Steps.refl Step.pushr
    constructor
    · apply ContinuesWith.val
    constructor
    · apply Represents.bool
    · intro _ _ h_lookup
      assumption
  | succr e ih =>
    -- wow learning this tactic would have made earlier proofs a lot more concise
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push 1, .op .plus] ++ is) rel
    simp [compile, List.append_assoc]
    cases cont
    exists (x + 1), h', is, cs, (x + 1) :: s
    constructor
    · apply Steps.trans (Steps.trans steps Step.pushr) (Step.opr OpEval.plus)
    constructor
    · apply ContinuesWith.val
    constructor
    · cases repr
      apply Represents.int
    assumption
  | predr e ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push (-1), .op .plus] ++ is) rel
    simp [compile, List.append_assoc]
    cases cont
    exists (x - 1), h', is, cs, (x - 1) :: s
    constructor
    · apply Steps.trans (Steps.trans steps Step.pushr) (Step.opr OpEval.plus)
    constructor
    · apply ContinuesWith.val
    constructor
    · cases repr
      apply Represents.int
    assumption
  | succ_propr e ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push 1, .op .plus] ++ is) rel
    exists x, h', is', cs', s'
    simp [compile, List.append_assoc]
    constructor
    · assumption
    constructor
    · apply exn_lemma
      assumption
    constructor
    assumption
    assumption
  | pred_propr e ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ := ih (is := [.push (-1), .op .plus] ++ is) rel
    exists x, h', is', cs', s'
    simp [compile, List.append_assoc]
    constructor
    · assumption
    constructor
    · apply exn_lemma
      assumption
    constructor
    assumption
    assumption
  | plusr evl evr ihl ihr =>
    rename_i r el il er ir
    -- draw from the first inductive hypothesis
    obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
      ihl (is := compile ds (none :: c) er ++ Instr.op Op.plus :: is) rel
    cases contl
    -- show the heap and env are stable through compiling the first expr?
    have rel_stable : Related s c r hl' := Related.mono rel extnl
    have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable
    -- now that we have a new relation that represents the state after compiling
    -- we can go ahead and use the second hypothesis
    obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
      ihr (is := Instr.op Op.plus :: is) rel_r
    cases contr
    -- show the conjunction holds
    exists (xl + xr), hr', is, cs, (xl + xr) :: s
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps stepsl
      apply Steps.trans_steps stepsr
      apply Steps.trans Steps.refl
      apply Step.opr OpEval.plus
    constructor
    · apply ContinuesWith.val
    constructor
    · cases reprl
      cases reprr
      apply Represents.int
    intros _ _ lookup
    apply extnr
    apply extnl
    assumption
  | timesr evl evr ihl ihr =>
    rename_i r el il er ir
    obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
      ihl (is := compile ds (none :: c) er ++ Instr.op Op.times :: is) rel
    cases contl

    have rel_stable : Related s c r hl' := Related.mono rel extnl
    have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable

    obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
      ihr (is := Instr.op Op.times :: is) rel_r
    cases contr

    exists (xl * xr), hr', is, cs, (xl * xr) :: s
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps stepsl
      apply Steps.trans_steps stepsr
      apply Steps.trans Steps.refl
      apply Step.opr OpEval.mult
    constructor
    · apply ContinuesWith.val
    constructor
    · cases reprl
      cases reprr
      apply Represents.int
    intros _ _ lookup
    apply extnr
    apply extnl
    assumption
  -- compiling the left expr gives us an error
  | plus_proplr evl ihl =>
    rename_i _ _ _ er
    obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
      ihl (cs := cs) (is := compile ds (none :: c) er ++ Instr.op Op.plus :: is) rel
    exists xl, hl', isl', csl', sl'
    constructor
    · simp [compile, List.append_assoc]
      assumption
    constructor
    · apply exn_lemma
      assumption
    constructor
    assumption
    assumption
  | plus_proprr evl evr ihl ihr =>
    rename_i r _ er _ _
    obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
      ihl (is := compile ds (none :: c) er ++ Instr.op Op.plus :: is) rel
    cases contl

    have rel_stable : Related s c r hl' := Related.mono rel extnl
    have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable

    obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
      ihr (is := Instr.op Op.plus :: is) rel_r
    cases contr with | exn =>

    exists xr, hr', isr', csr', sr'
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps stepsl
      exact stepsr

    constructor
    · apply exn_lemma
      apply ContinuesWith.exn
      assumption
    constructor
    assumption
    intros _ _ lookup
    apply extnr
    apply extnl
    assumption
  | times_proplr evl ihl =>
    rename_i er
    obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
      ihl (cs := cs) (is := compile ds (none :: c) er ++ Instr.op Op.times :: is) rel
    exists xl, hl', isl', csl', sl'
    constructor
    · simp [compile, List.append_assoc]
      assumption
    constructor
    · apply exn_lemma
      assumption
    constructor
    assumption
    assumption
  | times_proprr evl evr ihl ihr =>
    rename_i r _ er _ _
    obtain ⟨ xl, hl', isl', csl', sl', stepsl, contl, reprl, extnl ⟩ :=
      ihl (is := compile ds (none :: c) er ++ Instr.op Op.times :: is) rel
    cases contl

    have rel_stable : Related s c r hl' := Related.mono rel extnl
    have rel_r : Related (xl :: s) (none :: c) r hl' := Related.push rel_stable

    obtain ⟨ xr, hr', isr', csr', sr', stepsr, contr, reprr, extnr ⟩ :=
      ihr (is := Instr.op Op.times :: is) rel_r
    cases contr with | exn =>

    exists xr, hr', isr', csr', sr'
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps stepsl
      exact stepsr

    constructor
    · apply exn_lemma
      apply ContinuesWith.exn
      assumption
    constructor
    assumption
    intros _ _ lookup
    apply extnr
    apply extnl
    assumption
  | iftr evg evt ihg iht =>
    rename_i r eg et _ ef
    obtain ⟨ xg, hg', isg', csg', sg', stepsg, contg, reprg, extng ⟩ :=
      ihg (is := Instr.branch (compile ds c et) (compile ds c ef) :: is) rel
    cases contg
    cases reprg
    have rel_stable : Related s c r hg' := Related.mono rel extng
    obtain ⟨ xt, ht', ist', cst', st', stepst, contt, reprt, extnt ⟩ := iht (is := is) rel_stable
    cases contt with
    | val =>
      exists xt, ht', is, cs, (xt :: s)
      constructor
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchtr)
        assumption
      constructor
      · apply ContinuesWith.val
      constructor
      assumption
      intros _ _ look
      apply extnt
      apply extng
      assumption
    | exn =>
      exists xt, ht', ist', cst', st'
      constructor
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchtr)
        assumption
      constructor
      · apply ContinuesWith.exn
        assumption
      constructor
      assumption
      intros _ _ look
      · apply extnt
        apply extng
        assumption
  | iffr evg evf ihg ihf =>
    rename_i r eg ef _ et
    obtain ⟨xg, hg', isg', csg', sg', stepsg, contg, reprg, extng⟩ :=
      ihg (is := Instr.branch (compile ds c et) (compile ds c ef) :: is) rel
    cases contg
    cases reprg
    have rel_stable : Related s c r hg' :=
      Related.mono rel extng
    obtain ⟨xf, hf', isf', csf', sf', stepsf, contf, reprf, extnf⟩ :=
      ihf (is := is) rel_stable
    cases contf with
    | val =>
      refine ⟨xf, hf', is, cs, xf :: s, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchfr)
        assumption
      · apply ContinuesWith.val
      · assumption
      · intro a v look
        apply extnf
        apply extng
        assumption
    | exn h_exn =>
      refine ⟨xf, hf', isf', csf', sf', ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps stepsg
        apply Steps.trans_steps (Steps.trans Steps.refl Step.branchfr)
        assumption
      · apply ContinuesWith.exn
        assumption
      · assumption
      · intro a v look
        apply extnf
        apply extng
        assumption
  | if_propr evg ihg =>
    rename_i r eg v et ef
    obtain ⟨xg, hg', isg', csg', sg', stepsg, contg, reprg, extng⟩ :=
      ihg (is := Instr.branch (compile ds c et) (compile ds c ef) :: is) rel
    refine ⟨xg, hg', isg', csg', sg', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | negtr ev ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ :=
      ih (is := Instr.op Op.flip :: is) rel
    cases cont
    cases repr
    exists 0, h', is, cs, (0 :: s)
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps
      apply Steps.trans Steps.refl
      apply Step.opr OpEval.flip1
    constructor
    · apply ContinuesWith.val
    constructor
    · apply Represents.bool
    · assumption
  | negfr ev ih =>
    obtain ⟨ x, h', is', cs', s', steps, cont, repr, extn ⟩ :=
      ih (is := Instr.op Op.flip :: is) rel
    cases cont
    cases repr
    exists 1, h', is, cs, (1 :: s)
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps
      apply Steps.trans Steps.refl
      apply Step.opr OpEval.flip0
    constructor
    · apply ContinuesWith.val
    constructor
    · apply Represents.bool
    · assumption
  | neg_propr ev ih =>
    rename_i r e v
    obtain ⟨x, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.op .flip] ++ is) rel
    refine ⟨x, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | bindr ev1 ev2 ih1 ih2 =>
    rename_i r e1 v1 x a e2
    obtain ⟨i1, h1, is1, cs1, s1, steps1, cont1, repr1, ext1⟩ :=
      ih1
        (is := compile ds (some x :: c) e2 ++ ([.exch, .pop] ++ is))
        rel
    cases cont1
    have rel_h1 : Related s c r h1 :=
      Related.mono rel ext1
    have rel_body : Related (i1 :: s) (some x :: c) ((x, v1) :: r) h1 :=
      Related.bind rel_h1 repr1
    obtain ⟨i2, h2, is2, cs2, s2, steps2, cont2, repr2, ext2⟩ :=
      ih2
        (is := [.exch, .pop] ++ is)
        rel_body
    cases cont2 with
    | val =>
      refine ⟨i2, h2, is, cs, i2 :: s, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps steps1
        apply Steps.trans_steps steps2
        apply Steps.trans
        · apply Steps.trans Steps.refl
          apply Step.exchr
        · apply Step.popr
      · apply ContinuesWith.val
      · assumption
      · intro aa vv hlookup
        apply ext2
        apply ext1
        assumption
    | exn h_exn =>
      refine ⟨i2, h2, is2, cs2, s2, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        repeat rw [List.append_assoc]
        apply Steps.trans_steps steps1
        assumption
      · apply exn_lemma
        apply ContinuesWith.exn
        assumption
      · assumption
      · intro aa vv hlookup
        apply ext2
        apply ext1
        assumption
  | bind_propr ev ih =>
    rename_i e1 v x e2
    obtain ⟨i, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih
        (is := compile ds (some x :: c) e2 ++ ([.exch, .pop] ++ is))
        rel
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | call_propr ev ih =>
    rename_i r e f v
    obtain ⟨i, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih
        (is := (match Defns.indexOf ds f with
                | some n => [.push (Int.ofNat n), .call, .exch, .pop]
                | none => []) ++ is)
        rel
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | fst_propr ev ih =>
    rename_i r e v
    obtain ⟨i, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.read 0] ++ is) rel
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | snd_propr ev ih =>
    rename_i r e v
    obtain ⟨i, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.read 1] ++ is) rel
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | throw_propr ev ih =>
    rename_i r e v
    obtain ⟨i, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.abort] ++ is) rel
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | pair_proplr ev ih =>
    rename_i r e1 v e2
    obtain ⟨i, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih
        (is := compile ds (none :: c) e2 ++ ([.alloc 2, .write 1, .write 0] ++ is))
        rel
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | pair_proprr ev1 ev2 ih1 ih2 =>
    rename_i r e1 e2 v1 v2
    obtain ⟨i1, h1, is1, cs1, s1, steps1, cont1, repr1, ext1⟩ :=
      ih1
        (is := compile ds (none :: c) e2 ++ ([.alloc 2, .write 1, .write 0] ++ is))
        rel
    cases cont1
    have rel_h1 : Related s c r h1 :=
      Related.mono rel ext1
    have rel_e2 : Related (i1 :: s) (none :: c) r h1 :=
      Related.push rel_h1
    obtain ⟨i2, h2, is2, cs2, s2, steps2, cont2, repr2, ext2⟩ :=
      ih2
        (is := [.alloc 2, .write 1, .write 0] ++ is)
        rel_e2
    cases cont2 with
    | exn h_exn =>
      refine ⟨i2, h2, is2, cs2, s2, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps steps1
        assumption
      · apply exn_lemma
        apply ContinuesWith.exn
        assumption
      · assumption
      · intro aa vv hlookup
        apply ext2
        apply ext1
        assumption
  | varr hlook =>
    obtain ⟨n, i, hc, hs, hrepr⟩ := Related.lookup rel hlook
    refine ⟨i, h, is, cs, i :: s, ?_, ?_, ?_, ?_⟩
    · simp [compile]
      rw [hc]
      apply Steps.trans Steps.refl
      apply Step.getr
      assumption
    · apply ContinuesWith.val
    · assumption
    · intro aa vv hlookup
      assumption
  | fstr ev ih =>
    rename_i r e v1 v2
    obtain ⟨ipair, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.read 0] ++ is) rel
    cases cont
    cases repr with
    | pair repr1 repr2 look1 look2 =>
      rename_i i1 i2
      refine ⟨i1, h', is, cs, i1 :: s, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans
        · assumption
        · apply Step.readr
          assumption
      · apply ContinuesWith.val
      · assumption
      · assumption
  | sndr ev ih =>
    rename_i r e v1 v2
    obtain ⟨ipair, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.read 1] ++ is) rel
    cases cont
    cases repr with
    | pair repr1 repr2 look1 look2 =>
      rename_i i1 i2
      refine ⟨i2, h', is, cs, i2 :: s, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans
        · assumption
        · apply Step.readr
          assumption
      · apply ContinuesWith.val
      · assumption
      · assumption
  | callr eva hlookup evbody iha ihbody =>
    rename_i r e v1 f x e' a
    obtain ⟨iarg, h1, is1, cs1, s1, steps1, cont1, repr1, ext1⟩ :=
      iha
        (is := (match Defns.indexOf ds f with
                | some n => [.push (Int.ofNat n), .call, .exch, .pop]
                | none => []) ++ is)
        rel
    cases cont1
    obtain ⟨n, hnidx, hncode⟩ := RelatedDefns.lookup hlookup
    have rel_fun : Related (iarg :: s) [some x] [(x, v1)] h1 :=
      Related.bind Related.mt repr1
    obtain ⟨ibody, h2, is2, cs2, s2, steps2, cont2, repr2, ext2⟩ :=
      ihbody
        (is := [.exch, .pop] ++ is)
        rel_fun
    cases cont2 with
    | val =>
      refine ⟨ibody, h2, is, cs, ibody :: s, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps steps1
        rw [hnidx]
        apply Steps.trans_steps
        · apply Steps.trans
          · apply Steps.trans Steps.refl
            apply Step.pushr
          · apply Step.callr
            simpa using hncode
        apply Steps.trans_steps steps2
        apply Steps.trans
        · apply Steps.trans Steps.refl
          apply Step.exchr
        · apply Step.popr
      · apply ContinuesWith.val
      · assumption
      · intro aa vv hlook
        apply ext2
        apply ext1
        assumption
    | exn h_exn =>
      refine ⟨ibody, h2, is2, cs2, s2, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps steps1
        rw [hnidx]
        apply Steps.trans_steps
        · apply Steps.trans
          · apply Steps.trans Steps.refl
            apply Step.pushr
          · apply Step.callr
            simpa using hncode
        assumption
      · apply exn_lemma
        apply ContinuesWith.exn
        assumption
      · assumption
      · intro aa vv hlook
        apply ext2
        apply ext1
        assumption
  | throwr ev ih =>
    rename_i r e v
    obtain ⟨i, h', is1, cs1, s1, steps, cont, repr, extn⟩ :=
      ih (is := [.abort] ++ is) rel
    cases cont
    obtain ⟨is', cs', s', abortsteps, exncont⟩ :=
      abort_exists_steps
        (ds := compile_defns ds)
        (is := is)
        (cs := cs)
        (i := i)
        (s := s)
        (h := h')
    refine ⟨i, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps
      assumption
    · apply ContinuesWith.exn
      assumption
    · assumption
    · assumption
  | handle_valr ev ih =>
    rename_i r e v f
    obtain ⟨i, h', isb, csb, sb, stepsb, contb, repr, extn⟩ :=
      ih
        (is := ([] : Instrs))
        (cs := Frame.handler
          (match Defns.indexOf ds f with
           | some n => [.push (Int.ofNat n), .call, .exch, .pop]
           | none => [])
          is s :: cs)
        rel
    cases contb
    have stepsb' :
      Steps (compile_defns ds)
        (compile ds c e)
        (Frame.handler
          (match Defns.indexOf ds f with
           | some n => [.push (Int.ofNat n), .call, .exch, .pop]
           | none => [])
          is s :: cs)
        s h
        ([] : Instrs)
        (Frame.handler
          (match Defns.indexOf ds f with
           | some n => [.push (Int.ofNat n), .call, .exch, .pop]
           | none => [])
          is s :: cs)
        (i :: s) h' := by
      simpa using stepsb
    refine ⟨i, h', is, cs, i :: s, ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps
      · apply Steps.trans Steps.refl
        apply Step.trycatchr
      apply Steps.trans_steps stepsb'
      apply Steps.trans Steps.refl
      apply Step.ret_handler
    · apply ContinuesWith.val
    · assumption
    · assumption
  | handle_exnr ev hlookup evh ihbody ihhandler =>
    rename_i r e v f x e' a
    obtain ⟨iexn, h1, isb, csb, sb, stepsb, contb, repr_exn, ext1⟩ :=
      ihbody
        (is := ([] : Instrs))
        (cs := Frame.handler
          (match Defns.indexOf ds f with
           | some n => [.push (Int.ofNat n), .call, .exch, .pop]
           | none => [])
          is s :: cs)
        rel
    cases contb with
    | exn hcw =>
      cases hcw
      have stepsb' :
        Steps (compile_defns ds)
          (compile ds c e)
          (Frame.handler
            (match Defns.indexOf ds f with
             | some n => [.push (Int.ofNat n), .call, .exch, .pop]
             | none => [])
            is s :: cs)
          s h
          (match Defns.indexOf ds f with
           | some n => [.push (Int.ofNat n), .call, .exch, .pop]
           | none => [])
          (Frame.ret is :: cs)
          (iexn :: s) h1 := by
        simpa using stepsb
      obtain ⟨n, hnidx, hncode⟩ := RelatedDefns.lookup hlookup
      have rel_handler : Related (iexn :: s) [some x] [(x, v)] h1 :=
        Related.bind Related.mt repr_exn
      obtain ⟨ires, h2, ish, csh, sh, stepsh, conth, reprh, ext2⟩ :=
        ihhandler
          (is := [.exch, .pop])
          (cs := Frame.ret is :: cs)
          rel_handler
      cases conth with
      | val =>
        refine ⟨ires, h2, is, cs, ires :: s, ?_, ?_, ?_, ?_⟩
        · simp [compile, List.append_assoc]
          apply Steps.trans_steps
          · apply Steps.trans Steps.refl
            apply Step.trycatchr
          apply Steps.trans_steps stepsb'
          rw [hnidx]
          apply Steps.trans_steps
          · apply Steps.trans
            · apply Steps.trans Steps.refl
              apply Step.pushr
            · apply Step.callr
              simpa using hncode
          apply Steps.trans_steps stepsh
          apply Steps.trans_steps
          · apply Steps.trans
            · apply Steps.trans Steps.refl
              apply Step.exchr
            · apply Step.popr
          apply Steps.trans Steps.refl
          apply Step.retr
        · apply ContinuesWith.val
        · assumption
        · intro aa vv hlook
          apply ext2
          apply ext1
          assumption
      | exn h_handler_exn =>
        cases h_handler_exn with
        | exn_ret h_tail =>
          refine ⟨ires, h2, ish, csh, sh, ?_, ?_, ?_, ?_⟩
          · simp [compile, List.append_assoc]
            apply Steps.trans_steps
            · apply Steps.trans Steps.refl
              apply Step.trycatchr
            apply Steps.trans_steps stepsb'
            rw [hnidx]
            apply Steps.trans_steps
            · apply Steps.trans
              · apply Steps.trans Steps.refl
                apply Step.pushr
              · apply Step.callr
                simpa using hncode
            assumption
          · apply exn_lemma
            apply ContinuesWith.exn
            assumption
          · assumption
          · intro aa vv hlook
            apply ext2
            apply ext1
            assumption
  | pairr ev1 ev2 ih1 ih2 =>
    rename_i r e1 v1 e2 v2
    obtain ⟨i1, h1, is1, cs1, s1, steps1, cont1, repr1, ext1⟩ :=
      ih1
        (is := compile ds (none :: c) e2 ++ ([.alloc 2, .write 1, .write 0] ++ is))
        rel
    cases cont1
    have rel_h1 : Related s c r h1 :=
      Related.mono rel ext1
    have rel_e2 : Related (i1 :: s) (none :: c) r h1 :=
      Related.push rel_h1
    obtain ⟨i2, h2, is2, cs2, s2, steps2, cont2, repr2, ext2⟩ :=
      ih2
        (is := [.alloc 2, .write 1, .write 0] ++ is)
        rel_e2
    cases cont2
    obtain ⟨a, fresh⟩ := exists_freshBlock h2 2
    let h3 := ((h2.ext (a + 1) i2).ext (a + 0) i1)
    have h3ext : HeapExtends h2 h3 := by
      exact HeapExtends.allocPair fresh
    have h1_h3 : HeapExtends h1 h3 := by
      apply HeapExtends.trans ext2 h3ext
    have h_h3 : HeapExtends h h3 := by
      apply HeapExtends.trans ext1 h1_h3
    refine ⟨a, h3, is, cs, a :: s, ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps1
      apply Steps.trans_steps steps2
      apply Steps.trans
      · apply Steps.trans
        · apply Steps.trans Steps.refl
          apply Step.allocr
          assumption
        · apply Step.writer
      · apply Step.writer
    · apply ContinuesWith.val
    · apply Represents.pair
      · apply Represents.mono repr1
        assumption
      · apply Represents.mono repr2
        assumption
      · simp [Heap.ext, Heap.lookup, h3]
      · simp [Heap.ext, Heap.lookup, h3]
        omega
    · assumption
  | vec_nilr =>
    obtain ⟨ptr, fresh⟩ := exists_freshBlock h 0
    refine ⟨ptr, h, is, cs, ptr :: s, ?_, ?_, ?_, ?_⟩
    · simp [compile, build_vec]
      apply Steps.trans Steps.refl
      apply Step.allocr
      exact fresh
    · apply ContinuesWith.val
    · apply Represents.vec (fun _ => 0)
      · intro k v hk; simp at hk
      · intro k v hk; simp at hk
    · intro a v hlook; assumption
  | vec_consr => sorry
  | vec_proplr eve ihe =>
    rename_i r e es _
    -- get the pointer to the fresh block (we will need this when proving steps)
    obtain ⟨ ptr, fresh ⟩ := exists_freshBlock h (es.length + 1)

    -- update our relation with new stack
    have rel_alloc : Related (ptr :: s) (none :: c) r h := Related.push rel

    -- now we can use inductive hypothesis
    obtain ⟨ exn, h', is', cs', s', steps, cont, repr, extn ⟩ :=
    -- res of is is swap and write and compilation of res of es
      ihe (is := [.exch, .write 0] ++ build_vec 1 es ds c ++ is) rel_alloc

    cases cont
    exists exn, h', is', cs', s'
    constructor
    · simp [compile, build_vec, List.append_assoc]
      apply Steps.trans_steps
      -- get allocation steps by itself
      · apply Steps.trans Steps.refl (Step.allocr fresh)
      · assumption
    constructor
    · apply exn_lemma
      apply ContinuesWith.exn
      assumption
    constructor
    assumption
    assumption
  | vec_proprr => sorry
  | vget_propr ev ih =>
    rename_i r e i v
    obtain ⟨iexn, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.read (Int.ofNat i)] ++ is) rel
    refine ⟨iexn, h', is', cs', s', ?_, ?_, ?_, ?_⟩
    · simp [compile, List.append_assoc]
      assumption
    · apply exn_lemma
      assumption
    · assumption
    · assumption
  | vgetr ev h_bounds ih =>
    rename_i r e i vs v
    obtain ⟨iptr, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (is := [.read (Int.ofNat i)] ++ is) rel
    cases cont
    cases repr with
    | vec ivs hrep_vs hlook_vs =>
      refine ⟨ivs i, h', is, cs, (ivs i) :: s, ?_, ?_, ?_, ?_⟩
      · simp [compile, List.append_assoc]
        apply Steps.trans_steps steps
        apply Steps.trans Steps.refl
        apply Step.readr
        apply hlook_vs i v h_bounds
      · apply ContinuesWith.val
      · apply hrep_vs i v h_bounds
      · assumption
  | vsetr => sorry
  | vset_proplr ev ih =>
    rename_i r e i e_v v
    obtain ⟨iptr, h', is', cs', s', steps, cont, repr, extn⟩ :=
      ih (cs := cs) (is := compile ds (none :: c) e_v ++ Instr.exch :: Instr.write (Int.ofNat i) :: is) rel
    exists iptr, h', is', cs', s'
    constructor
    · simp [compile, List.append_assoc]
      assumption
    constructor
    · apply exn_lemma
      assumption
    constructor
    assumption
    assumption
  | vset_proprr ev1 ev2 ih1 ih2 =>
    rename_i r e i e_v vs v
    obtain ⟨iptr, h1, is1, cs1, s1, steps1, cont1, repr1, ext1⟩ :=
      ih1 (is := compile ds (none :: c) e_v ++ Instr.exch :: Instr.write (Int.ofNat i) :: is) rel
    cases cont1
    have rel_stable : Related s c r h1 := Related.mono rel ext1
    have rel_e_v : Related (iptr :: s) (none :: c) r h1 := Related.push rel_stable

    obtain ⟨iv, h2, is2, cs2, s2, steps2, cont2, repr2, ext2⟩ :=
      ih2 (is := Instr.exch :: Instr.write (Int.ofNat i) :: is) rel_e_v
    cases cont2 with | exn h_exn =>

    exists iv, h2, is2, cs2, s2
    constructor
    · simp [compile, List.append_assoc]
      apply Steps.trans_steps steps1
      exact steps2
    constructor
    · apply exn_lemma
      apply ContinuesWith.exn
      assumption
    constructor
    · assumption
    · intro aa vv hlook
      apply ext2
      apply ext1
      assumption
