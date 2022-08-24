(* Monad Implementations *)

Require Import common.
Require Import Errors.
Require Import Events.
Require Import monad.
Require Import primitives.
Require Import Integers.
Require Import IR.
Require Import intpos.

Parameter mem_size : int.       (* maximum integer that can index the JIT memory *)

(** * State and Error Monad defs, parameterized by a state Type *)
(* This is the state and error monad definition that our free monad can be transformed into, *)
(* given a monadic specification of each primitive *)
Inductive sres (state:Type) (A:Type): Type :=
| SError : errmsg -> sres state A
| SOK: A -> state -> sres state A.
Arguments SOK [state A].
Arguments SError [state A].
Definition smon {state:Type} (A:Type) : Type := forall (s:state), sres state A.
Definition sret {state:Type} {A:Type} (x:A) : smon A :=
  fun (s:state) => SOK x s.
Definition serror {state:Type} {A:Type} (msg:errmsg) : smon A :=
  fun (s:state) => SError msg.
Definition sbind {state:Type} {A B:Type} (f: smon A) (g:A -> smon B) : smon B :=
  fun (s:state) =>
    match (f s) with
    | SError msg => SError msg
    | SOK a s' => g a s'
    end.

(** * Notations  *)
Definition sbind2 {S A B C: Type} (f: @smon S (A * B)) (g: A -> B -> @smon S C) : smon C :=
  sbind f (fun xy => g (fst xy) (snd xy)).

Definition sbind3 {S A B C D: Type} (v: @smon S (A * B * C)) (f: A -> B -> C -> @smon S D) : smon D :=
  sbind v (fun xyz => f (fst (fst xyz)) (snd(fst xyz)) (snd(xyz))).

Definition sbind4 {S A B C D E: Type} (v: @smon S (A * B * C * D)) (f: A -> B -> C -> D -> @smon S E) : smon E :=
  sbind v (fun abcd => f (fst (fst (fst abcd))) (snd (fst (fst abcd))) (snd (fst abcd)) (snd abcd)).

Notation "'do' X <<= A ; B" := (sbind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <<= A ; B" := (sbind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).
Notation "'do' ( X , Y , Z ) <<= A ; B" := (sbind3 A (fun X Y Z => B))
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).
Notation "'do' ( W , X , Y , Z ) <<= A ; B" := (sbind4 A (fun W X Y Z => B))
   (at level 200, W ident, X ident, Y ident, Z ident, A at level 100, B at level 200).

Definition sret' {A S: Type} (x: res A) : @smon S A :=
  match x with
  | OK a => sret a
  | Error s => serror s
  end.


(** * Monadic Laws for the State and Error Monad *)
Lemma state_left_id:
  forall (state X Y:Type) (x:X) (f:X -> @smon state Y),
    sbind (sret x) f = f x.
Proof.
  intros state X Y x f. simpl. auto.
Qed.

(* Is this only true for a non-empty state type? *)
Lemma state_right_id:
  forall (state X:Type) (f:@smon state X) (s:state),
    sbind f sret = f.
Proof.
  intros state X f s. destruct f.
  - auto.
  - unfold sbind. apply functional_extensionality. intros x. destruct (f x); auto.
  - unfold sbind. apply functional_extensionality. intros y. destruct (f y); auto.
Qed.

(* Is this only true for a non-empty state type? *)
Lemma state_assoc:
  forall (state X Y Z:Type) (f1: @smon state X) (f2: X -> smon Y) (f3: Y -> smon Z) (s:state),
    sbind (sbind f1 f2) f3 = sbind f1 (fun x => sbind (f2 x) f3).
Proof.
  intros state X Y Z f1 f2 f3 s. destruct f1.
  - auto.
  - unfold sbind. apply functional_extensionality. intros x. destruct (f1 x); auto.
  - unfold sbind. apply functional_extensionality. intros x0. destruct (f1 x0); auto.
Qed.

(** * Monad Implem  *)
(* A monad implem consists in a state type and primitives *)
Record monad_impl (mstate:Type): Type :=
  mk_mon_imp {
      init_state : mstate;
      prim_save: int -> @smon mstate unit;
      prim_load: @smon mstate int;
      prim_memset: int -> int -> @smon mstate unit;
      prim_memget: int -> @smon mstate int;
      prim_closesf: int -> int -> int -> @smon mstate unit;
      prim_opensf: @smon mstate open_sf;
      prim_pushirsf: IR_stackframe -> @smon mstate unit;
      prim_install_code: fun_id -> asm_fun -> @smon mstate unit;
      prim_load_code: asm_id -> @smon mstate Asm.program;
      prim_check_compiled: fun_id -> @smon mstate compiled_status
    }.

Arguments init_state [mstate].
Arguments prim_save [mstate].
Arguments prim_load [mstate].
Arguments prim_memset [mstate].
Arguments prim_memget [mstate].
Arguments prim_closesf [mstate].
Arguments prim_opensf [mstate].
Arguments prim_pushirsf [mstate].
Arguments prim_install_code [mstate].
Arguments prim_load_code [mstate].
Arguments prim_check_compiled [mstate].


(* Getting the state monad associated to each primitive *)
Definition exec_prim {R S:Type} (p:primitive R) (i:monad_impl S) : @smon S R :=
  match p with
  | Prim_Save x => (prim_save i) x
  | Prim_Load => (prim_load i)
  | Prim_MemSet x y => (prim_memset i) x y
  | Prim_MemGet x => (prim_memget i) x
  | Prim_CloseSF a b c => (prim_closesf i) a b c
  | Prim_OpenSF => (prim_opensf i)
  | Prim_PushIRSF sf => (prim_pushirsf i) sf
  | Prim_Install_Code fid asf => (prim_install_code i) fid asf
  | Prim_Load_Code aid => (prim_load_code i) aid
  | Prim_Check_Compiled fid => (prim_check_compiled i) fid
  end.

(** * Giving Semantics to a free monad *)
Fixpoint exec {A S:Type} (f:free A) (i:monad_impl S): @smon S A :=
  match f with
  | pure a => sret a
  | impure prim cont =>
    sbind (exec_prim prim i) (fun r => exec (cont r) i)
  | ferror e => serror e
  end.


(** * Naive Implementation  *)
Definition asm_codes : Type := PTree.t asm_fun.
Definition nocode: asm_codes := (PTree.empty asm_fun).

Definition memory : Type := PTree.t int.
Definition init_mem : memory := PTree.empty int.

Record mutables: Type := mkmut {
  state_stack: stack;
  state_stacktop: env;
  state_mem: memory;
                          }.

Definition n_state : Type := mutables * asm_codes.

Definition init_mutables : mutables :=
  mkmut nil nil init_mem.

Definition init_nc_state (nc:asm_codes) : n_state :=
  (init_mutables, nc).

Definition init_n_state : n_state :=
  (init_mutables, nocode).

Definition mut: n_state -> mutables := fst.
Definition cod: n_state -> asm_codes := snd.

Definition n_save (x:int) : smon unit :=
  fun s =>
    SOK tt (mkmut (state_stack (mut s)) (x::state_stacktop (mut s)) (state_mem (mut s)), cod s).

Definition n_load : smon int :=
  fun s =>
    match (state_stacktop (mut s)) with
    | nil => SError ((MSG "Loading unsaved value")::nil)
    | x::top => SOK x (mkmut (state_stack (mut s)) top (state_mem (mut s)), (cod s))
    end.


Definition n_memset (x:int) (y:int) : smon unit :=
  fun s =>
    match (Int.lt x mem_size) with
    | true =>
      SOK tt (mkmut (state_stack (mut s)) (state_stacktop (mut s))
                    (PTree.set (intpos.pos_of_int x) y (state_mem (mut s))), cod s)
    | false => SError ((MSG "MemSet out of Mem Range")::nil)
    end.

Definition n_memget (x:int) : smon int :=
  fun s =>
    match (Int.lt x mem_size) with
    | true =>
      match (PTree.get (intpos.pos_of_int x) (state_mem (mut s))) with
      | Some y => SOK y s
      | None => SError ((MSG "MemGet Unset Address")::nil)
      end
    | false => SError ((MSG "MemGet out of Mem Range")::nil)
    end.


Definition n_closesf (caller cont_lbl retreg:int) : smon unit :=
  fun s =>
    SOK tt (mkmut (ASM_SF(caller, cont_lbl, retreg, state_stacktop (mut s))::(state_stack (mut s))) nil (state_mem (mut s)), cod s).

Definition n_push_interpreter_stackframe (irsf: IR_stackframe) : smon unit :=
  fun s =>
    match (state_stacktop (mut s)) with
    | nil => 
      SOK tt (mkmut ((IR_SF irsf)::(state_stack (mut s))) (state_stacktop (mut s)) (state_mem (mut s)), cod s)
    | _ =>
      SError ((MSG "Stacktop not empty")::nil)
    end.

Definition n_open_stackframe  : smon open_sf :=
  fun s =>
    match (state_stacktop (mut s)) with
    | nil => 
      match (state_stack (mut s)) with
      | nil => SOK empty_stack s
      | (IR_SF isf)::stk =>
        SOK (ir_sf isf) (mkmut stk nil (state_mem (mut s)), cod s)
      | (ASM_SF (caller, cont, retreg, lives))::stk =>
        SOK (nat_sf caller cont retreg)
            (mkmut stk lives (state_mem (mut s)), cod s)
      end
    | _ =>
      SError ((MSG "Non-empty Stacktop")::nil)
    end.


Definition n_install_code (fid:fun_id) (af: asm_fun): smon unit :=
  fun s => SOK tt (mkmut (state_stack (mut s)) (state_stacktop (mut s)) (state_mem (mut s)), ((cod s)#fid <- af)).

Definition n_load_prog_code (fid:fun_id) : smon asm_fun :=
  fun s =>
    match ((cod s)#fid) with
    | None => SError ((MSG "Loading unknown code")::nil)
    | Some af => SOK af s        (* no state modification *)
    end.


Definition n_load_code (aid:asm_id) : smon Asm.program :=
  match aid with
  | Call_id fid =>
    do asmf <<= n_load_prog_code fid;
      sret (fst asmf)
  | Cont_id fid cont_lbl =>
    do asmf <<= n_load_prog_code fid;
      match (PTree.get cont_lbl (snd asmf)) with
      | None => serror ((MSG "Can't find this continuation")::nil)
      | Some cont => SOK cont
      end
  end.
                   
Definition n_check_compiled (fid:fun_id) : smon compiled_status :=
  fun s =>
    match ((cod s)#fid) with
    | None => SOK Not_compiled s
    | Some af => SOK (Installed af) s
    end.

Definition naive_impl: monad_impl n_state :=
  mk_mon_imp n_state init_n_state n_save n_load n_memset n_memget
             n_closesf n_open_stackframe n_push_interpreter_stackframe
             n_install_code n_load_code
             n_check_compiled.
             

(** * Array Implementation  *)

Definition map_memory : Type := PMap.t int.
Definition init_map_mem : map_memory := PMap.init Int.zero.
(* default value is 0 *)
Definition stack_array := list int.
Record a_state: Type := amkstate {
  a_stack: stack_array;
  a_irstk: list IR_stackframe;
  a_mem: map_memory;
  a_nat_code: asm_codes;
                          }.

(* Identifiers for the array *)
Definition EMPTY : int := Int.zero.
Definition IR_ID : int := Int.one.
Definition NAT_ID : int := Int.repr 2.

Definition init_a_state : a_state :=
  amkstate (EMPTY::nil) nil init_map_mem nocode.

Definition a_save (x:int) : smon unit :=
  fun s =>
    SOK tt (amkstate (x::a_stack s) (a_irstk s) (a_mem s) (a_nat_code s)).

Definition a_load : smon int :=
  fun s =>
    match (a_stack s) with
    | nil => SError ((MSG "Loading unsaved value")::nil)
    | x::top => SOK x (amkstate top (a_irstk s) (a_mem s) (a_nat_code s))
    end.

Definition a_memset (x:int) (y:int) : smon unit :=
  fun s =>
    match (Int.lt x mem_size) with
    | true =>
      SOK tt (amkstate (a_stack s) (a_irstk s)
                       (PMap.set (intpos.pos_of_int x) y (a_mem s))
                       (a_nat_code s))
    | false => SError ((MSG "MemSet out of Mem Range")::nil)
    end.

Definition a_memget (x:int) : smon int :=
  fun s =>
    if (Int.lt x mem_size) then
      SOK (PMap.get (intpos.pos_of_int x) (a_mem s)) s
    else
      SError ((MSG "MemGet out of Mem Range")::nil).


Definition a_closesf (caller cont_lbl retreg:int): smon unit :=
  fun s =>
    SOK tt (amkstate (NAT_ID::caller::cont_lbl::retreg::(a_stack s)) (a_irstk s) (a_mem s) (a_nat_code s)).

Definition a_push_interpreter_stackframe (irsf: IR_stackframe) : smon unit :=
  fun s =>
    SOK tt (amkstate (IR_ID::(a_stack s)) (irsf::(a_irstk s)) (a_mem s) (a_nat_code s)).

Definition a_open_stackframe  : smon open_sf :=
  fun s =>
    match (a_stack s) with
    | nil => SError ((MSG "EMPTY id not found")::nil)
    | id::stk =>
      match (Int.eq id EMPTY) with
      | true => SOK empty_stack s
      | false =>
        match (Int.eq id IR_ID) with
        | true =>
          match (a_irstk s) with
          | nil => SError ((MSG "Missing IR stackframe")::nil)
          | irsf::irstk => SOK (ir_sf irsf) (amkstate stk irstk (a_mem s) (a_nat_code s))
          end
        | false =>
          match (Int.eq id NAT_ID) with
          | true =>
            match stk with
            | caller::cont::retreg::stk' =>
              SOK (nat_sf caller cont retreg)
                  (amkstate stk' (a_irstk s) (a_mem s) (a_nat_code s))
            | _ => SError ((MSG "Incomplete Native Stackframe")::nil)
            end
          | false => SError ((MSG "Unknown Stackframe ID")::nil)
          end
        end
      end
    end.


Definition a_install_code (fid:fun_id) (af: asm_fun): smon unit :=
  fun s => SOK tt (amkstate (a_stack s) (a_irstk s) (a_mem s) ((a_nat_code s)#fid <- af)).

Definition a_load_prog_code (fid:fun_id) : smon asm_fun :=
  fun s =>
    match ((a_nat_code s)#fid) with
    | None => SError ((MSG "Loading unknown code")::nil)
    | Some af => SOK af s        (* no state modification *)
    end.

Definition a_load_code (aid:asm_id) : smon Asm.program :=
  match aid with
  | Call_id fid =>
    do asmf <<= a_load_prog_code fid;
      sret (fst asmf)
  | Cont_id fid cont_lbl =>
    do asmf <<= a_load_prog_code fid;
      match (PTree.get cont_lbl (snd asmf)) with
      | None => serror ((MSG "Can't find this continuation")::nil)
      | Some cont => SOK cont
      end
  end.
                   
Definition a_check_compiled (fid:fun_id) : smon compiled_status :=
  fun s =>
    match ((a_nat_code s)#fid) with
    | None => SOK Not_compiled s
    | Some af => SOK (Installed af) s
    end.

Definition array_impl: monad_impl a_state :=
  mk_mon_imp a_state init_a_state a_save a_load a_memset a_memget
             a_closesf a_open_stackframe a_push_interpreter_stackframe
             a_install_code a_load_code
             a_check_compiled.
             


(** * Implementation Equivalence  *)
Record refines {istate jstate:Type} (i:monad_impl istate) (j:monad_impl jstate) :Type :=
  mk_ref {
      match_states: istate -> jstate -> Prop;
      match_init: match_states (init_state i) (init_state j);
      match_save:
        forall si si' x sj r,
          match_states si sj ->
          (prim_save i) x si = SOK r si' ->
          exists sj', (prim_save j) x sj = SOK r sj' /\ match_states si' sj';
      match_load:
        forall si si' sj r,
          match_states si sj ->
          (prim_load i) si = SOK r si' ->
          exists sj', (prim_load j) sj = SOK r sj' /\ match_states si' sj';
      match_memset:
        forall si si' x y sj r,
          match_states si sj ->
          (prim_memset i) x y si = SOK r si' ->
          exists sj', (prim_memset j) x y sj = SOK r sj' /\ match_states si' sj';
      match_memget:
        forall si si' x sj r,
          match_states si sj ->
          (prim_memget i) x si = SOK r si' ->
          exists sj', (prim_memget j) x sj = SOK r sj' /\ match_states si' sj';
      match_closesf:
        forall si si' a b c sj r,
          match_states si sj ->
          (prim_closesf i) a b c si = SOK r si' ->
          exists sj', (prim_closesf j) a b c sj = SOK r sj' /\ match_states si' sj';
      match_opensf:
        forall si si' sj r,
          match_states si sj ->
          (prim_opensf i) si = SOK r si' ->
          exists sj', (prim_opensf j) sj = SOK r sj' /\ match_states si' sj';
      match_pushirsf:
        forall si si' x sj r,
          match_states si sj ->
          (prim_pushirsf i) x si = SOK r si' ->
          exists sj', (prim_pushirsf j) x sj = SOK r sj' /\ match_states si' sj';
      match_install_code:
        forall si si' x y sj r,
          match_states si sj ->
          (prim_install_code i) x y si = SOK r si' ->
          exists sj', (prim_install_code j) x y sj = SOK r sj' /\ match_states si' sj';
      match_load_code:
        forall si si' x sj r,
          match_states si sj ->
          (prim_load_code i) x si = SOK r si' ->
          exists sj', (prim_load_code j) x sj = SOK r sj' /\ match_states si' sj';
      match_check_compiled:
        forall si si' x sj r,
          match_states si sj ->
          (prim_check_compiled i) x si = SOK r si' ->
          exists sj', (prim_check_compiled j) x sj = SOK r sj' /\ match_states si' sj';
    }.


(** * Correctness of the list impl  *)
Inductive match_stackframe: stackframe -> list int -> option IR_stackframe -> Prop :=
| match_irsf: forall isf,
    match_stackframe (IR_SF isf) ((IR_ID)::nil) (Some isf)
| match_natsf: forall caller cont_lbl retreg lives,
    match_stackframe (ASM_SF (caller, cont_lbl, retreg, lives)) (NAT_ID::caller::cont_lbl::retreg::lives) None.

(* append an option *)
Definition opt_app {A:Type} (o:option A) (l:list A) : list A :=
  match o with
  | None => l
  | Some a => a::l
  end.

Lemma opt_none:
  forall A (l:list A),
    l = opt_app None l.
Proof.
  intros A l. simpl. auto.
Qed.

Inductive match_stack: stack -> list int -> list IR_stackframe -> Prop :=
| match_empty:
    match_stack nil (EMPTY::nil) nil
| match_app:
    forall sf lsf stk l irl o newirl
      (MATCH_SF: match_stackframe sf lsf o)
      (MATCH_STACK: match_stack stk l irl)
      (OPT_APP: opt_app o irl = newirl),
      match_stack (sf::stk) (lsf ++ l) (newirl).

Inductive match_full_stack: stack -> env -> list int -> list IR_stackframe -> Prop :=
| match_full:
    forall stk top lstk irl
      (MATCH_STK: match_stack stk lstk irl),
      match_full_stack stk top (top ++ lstk) irl.

Definition match_mem (nm:memory) (mm:map_memory) : Prop :=
  forall addr v, PTree.get addr nm = Some v -> PMap.get addr mm = v.

Inductive ref_match_states: n_state -> a_state -> Prop :=
| matchs: forall stk top lstk irl nmem mmem codes
            (MATCH_STK: match_full_stack stk top lstk irl)
            (MATCH_HEAP: match_mem nmem mmem), 
    ref_match_states
      (mkmut stk top nmem, codes)
      (amkstate lstk irl mmem codes).
    
Theorem list_refine:
  refines naive_impl array_impl.
Proof.
  eapply mk_ref with (match_states := ref_match_states); unfold naive_impl, array_impl; simpl.
  - constructor. assert (match_full_stack nil nil (nil ++ (EMPTY::nil)) nil).
    constructor. constructor. simpl in H. auto.
    unfold match_mem, init_mem, init_map_mem. intros. rewrite PTree.gempty in H. inv H.
  - intros si si' x sj r H H0. inv H. unfold n_save in H0. inv H0. unfold a_save. 
    simpl. exists (amkstate (x::lstk) (irl) (mmem) (codes)). split; simpl; auto.
    constructor; auto. inv MATCH_STK. rewrite app_comm_cons. constructor; auto. 
  - intros si si' sj r H H0. inv H. unfold n_load in H0. simpl in H0.
    destruct top as [|x top'] eqn:TOP; inv H0. 
    unfold a_load. simpl. destruct lstk as [|y lstk']; inv MATCH_STK.
    exists (amkstate (top' ++ lstk) (irl) (mmem) (codes)). split; simpl; auto.
    constructor; auto. constructor; auto.
  - intros si si' x y sj r H H0. inv H. unfold n_memset in H0. inv H0. unfold a_memset.
    destruct (Int.lt x mem_size) eqn:MEMRANGE; inv H1.
    exists (amkstate lstk irl (PMap.set (pos_of_int x) y mmem) codes). split; simpl; auto.
    constructor; auto. auto.
    unfold match_mem. intros addr v H. poseq_destr (pos_of_int x) addr.
    + rewrite PTree.gss in H. inv H. rewrite PMap.gss. auto.
    + rewrite PTree.gso in H; auto. rewrite PMap.gso; auto.
  - intros si si' x sj r H H0. inv H. unfold n_memget in H0.
    destruct (Int.lt x mem_size) eqn:MEMRANGE; inv H0.
    destruct (nmem # (pos_of_int x)) eqn:MEMGET; inv H1. unfold a_memget.
    rewrite MEMRANGE. 
    exists (amkstate lstk irl mmem codes). split; simpl; auto. f_equal. auto.
    constructor; auto.
  - intros si si' a b c sj [] H H0. inv H. unfold n_closesf in H0. inv H0. unfold a_closesf.
    exists (amkstate (NAT_ID::a::b::c::lstk) irl mmem codes). split; simpl; auto.
    constructor; auto.
    replace (NAT_ID::a::b::c::lstk) with (nil ++ (NAT_ID::a::b::c::nil) ++ lstk) by auto.
    inv MATCH_STK. constructor; auto. rewrite app_assoc. econstructor; try constructor; auto.
  - intros si si' sj r H H0. inv H. unfold n_open_stackframe in H0. simpl in H0.
    destruct top; inv H0.
    inv MATCH_STK. unfold a_open_stackframe. simpl.
    destruct stk as [|[isf|asmsf] stk'].
    + inv MATCH_STK0. inv H1. rewrite Int.eq_true. exists (amkstate (EMPTY::nil) nil mmem codes).
      split; simpl; auto. constructor; auto. replace (EMPTY::nil) with (nil++(EMPTY::nil)) by auto.
      constructor. constructor.
    + inversion MATCH_STK0. subst. inversion MATCH_SF. subst. simpl. rewrite Int.eq_false.
      2: { intros H. inv H. }
      rewrite Int.eq_true. inv H1. exists (amkstate l irl0 mmem codes). split; simpl; auto.
      constructor; auto. replace l with (nil++l) by auto. constructor. auto.
    + inv MATCH_STK0. inv MATCH_SF. inv H1. simpl. rewrite Int.eq_false. rewrite Int.eq_false.
      2: { intros H. inv H. } 2: { intros H. inv H. }
      rewrite Int.eq_true. exists (amkstate (lives++l) irl0 mmem codes). split; simpl; auto.
      constructor; auto. constructor; auto.
  - intros si si' x sj r H H0. inv H. unfold n_push_interpreter_stackframe in H0. inv H0.
    destruct top; inv H1.
    unfold a_push_interpreter_stackframe. simpl.
    exists (amkstate (IR_ID::lstk) (x::irl) mmem codes). split; simpl; auto.
    constructor; auto. replace (IR_ID::lstk) with (nil++((IR_ID::nil) ++ lstk)) by auto.
    constructor; auto. inv MATCH_STK. econstructor; eauto. constructor; auto. simpl; auto.
  - intros si si' x y sj r H H0. inv H. unfold n_install_code in H0. inv H0. unfold a_install_code.
    simpl. exists (amkstate lstk irl mmem (codes # x <- y)). split; simpl; auto.
    constructor; auto.
  - intros si si' x sj r H H0. inv H. unfold n_load_code, n_load_prog_code in H0. inv H0.
    unfold a_load_code, a_load_prog_code, sbind. destruct x; unfold sbind in H1; simpl in H1. 
    + destruct (codes ! f) eqn:CODES; inv H1. exists (amkstate lstk irl mmem codes). simpl. rewrite CODES.
      split; simpl; auto. constructor; auto.
    + destruct (codes ! f) eqn:CODES; inv H1. exists (amkstate lstk irl mmem codes). simpl. rewrite CODES.
      destruct a. simpl in H0. simpl. destruct (t # l) eqn:FIND; inv H0.
    split; simpl; auto. constructor; auto.
  - intros si si' x sj r H H0. inv H. unfold n_check_compiled in H0. inv H0.
    unfold a_check_compiled. simpl. destruct (codes ! x) eqn:CODES; inv H1; auto.
    + exists (amkstate lstk irl mmem codes). split; simpl; auto. constructor; auto.
    + exists (amkstate lstk irl mmem codes). split; simpl; auto. constructor; auto.
Qed.


(** * Tactics to reason about state monads *)
Lemma exec_bind:
  forall (state A B:Type) (i:monad_impl state) (a:free A) (b: A -> free B),
    exec (fbind a b) i = sbind (exec a i) (fun x => exec (b x) i).
Proof.
  intros state A B i a b. induction a; simpl.
  - unfold sbind. simpl. auto.
  - unfold sbind. apply functional_extensionality. intros s.
    destruct (exec_prim prim i s) eqn:PRIM; auto. rewrite H. unfold sbind. auto.
  - unfold sbind. simpl. auto.
Qed.

Lemma exec_bind2:
  forall (state A B C:Type) (i:monad_impl state) (a:free (A * B)) (b: A -> B -> free C),
    exec (fbind2 a b) i = sbind2 (exec a i) (fun x y => exec (b x y) i).
Proof.
  intros state A B C i a b. unfold sbind2. unfold fbind2. rewrite exec_bind. auto.
Qed.

Lemma exec_bind3:
  forall (state A B C D:Type) (i:monad_impl state) (a:free (A * B * C)) (b: A -> B -> C -> free D),
    exec (fbind3 a b) i = sbind3 (exec a i) (fun x y z => exec (b x y z) i).
Proof.
  intros state A B C D i a b. unfold sbind3. unfold fbind3. rewrite exec_bind. auto.
Qed.

Lemma exec_bind4:
  forall (state A B C D E:Type) (i:monad_impl state) (a:free (A * B * C * D)) (b: A -> B -> C -> D -> free E),
    exec (fbind4 a b) i = sbind4 (exec a i) (fun x y z t => exec (b x y z t) i).
Proof.
  intros state A B C D E i a b. unfold sbind4. unfold fbind4. rewrite exec_bind. auto.
Qed.



Lemma bind_error:
  forall {state A B:Type} (i:monad_impl state) (a:free A) (b:A -> free B) c d ms,
    exec (fbind a b) i ms = c ->
    exec a i ms = SError d ->
    c = SError d.
Proof.
  intros state A B i a b c d ms H H0. rewrite exec_bind in H. unfold sbind in H. rewrite H0 in H. subst. auto.
Qed.

Lemma bind_ok:
  forall {state A B:Type} (i:monad_impl state) (a:free A) (b:A -> free B) c d ms ms1,
    exec (fbind a b) i ms = c ->
    exec a i ms = SOK d ms1 ->
    exec (b d) i ms1 = c.
Proof.
  intros state A B i a b c d ms ms1 H H0. rewrite exec_bind in H. unfold sbind in H. rewrite H0 in H. auto.
Qed.

Lemma sbind_error:
  forall {state A B:Type} (a:@smon state A) (b:A -> @smon state B) c d ms,
    (sbind a b) ms = c ->
    a ms = SError d ->
    c = SError d.
Proof.
  intros state A B a b c d ms H H0. unfold sbind in H. rewrite H0 in H. subst. auto.
Qed.

Lemma sbind_ok:
  forall {state A B:Type} (a:@smon state A) (b:A -> @smon state B) c d ms ms1,
    (sbind a b) ms = c ->
    a ms = SOK d ms1 ->
    (b d) ms1 = c.
Proof.
  intros state A B a b c d ms ms1 H H0. unfold sbind in H. rewrite H0 in H. auto.
Qed.

Ltac sdo_ok:=
  let HDO := fresh "HDO" in
  let HC := fresh "HC" in
  match goal with
  | [ H: exec (do V <<- ?a; ?b) ?i ?ms = SOK ?r ?ms' |- _ ] =>
    destruct (exec a i ms) eqn:HDO;
    [ specialize (bind_error _ _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (bind_ok _ _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: exec (do (X,Y) <<- ?a; ?b) ?i ?ms = SOK ?r ?ms' |- _ ] =>
    destruct (exec a i ms) eqn:HDO;
    [ specialize (bind_error _ _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (bind_ok _ _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: exec (do (X,Y,Z) <<- ?a; ?b) ?i ?ms = SOK ?r ?ms' |- _ ] =>
    destruct (exec a i ms) eqn:HDO;
    [ specialize (bind_error _ _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (bind_ok _ _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: exec (do (W,X,Y,Z) <<- ?a; ?b) ?i ?ms = SOK ?r ?ms' |- _ ] =>
    destruct (exec a i ms) eqn:HDO;
    [ specialize (bind_error _ _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (bind_ok _ _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: (do V <<= ?a; ?b) ?ms = SOK ?r ?ms' |- _ ] => 
    destruct (a ms) eqn:HDO;
    [ specialize (sbind_error _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (sbind_ok _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: (do (X,Y) <<= ?a; ?b) ?ms = SOK ?r ?ms' |- _ ] => 
    destruct (a ms) eqn:HDO;
    [ specialize (sbind_error _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (sbind_ok _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: (do (X,Y,Z) <<= ?a; ?b) ?ms = SOK ?r ?ms' |- _ ] => 
    destruct (a ms) eqn:HDO;
    [ specialize (sbind_error _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (sbind_ok _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H: (do (W,X,Y,Z) <<= ?a; ?b) ?ms = SOK ?r ?ms' |- _ ] => 
    destruct (a ms) eqn:HDO;
    [ specialize (sbind_error _ _ _ _ _ H HDO); intros HC; inv HC
    | specialize (sbind_ok _ _ _ _ _ _ H HDO); simpl; clear H; intros H ]
  | [ H : sret ?a ?ms = SOK ?r ?ms' |- _ ] => inv H
  | [ H : exec (fret ?a) ?i ?ms = SOK ?r ?ms' |- _ ] => inv H
  | [ H : exec (fret' ?a) ?i ?ms = SOK ?r ?ms' |- _ ] => destruct a eqn:HDO; inv H
  | [ H : exec (try_option ?a ?e) ?i ?ms = SOK ?r ?ms' |- _ ] => destruct a eqn:HDO; inv H
  end.

Lemma do_try:
  forall {state A B:Type} (a:A) e (b:A->free B) (i:monad_impl state),
    exec (fbind (try_option (Some a) e) b) i = exec (b a) i.
Proof.
  intros state A B a e b i. unfold try_option. simpl. auto.
Qed.

Lemma ret_ok':
  forall {A:Type} (a:A),
    exec (fret' (OK a)) naive_impl = sret a.
Proof.
  intros. unfold fret', sret. auto.
Qed.

Lemma do_ret:
  forall {state A B:Type} (a:A) (b:A -> @smon state B),
    sbind (sret a) b = b a.
Proof.
  intros state A B a b. unfold sbind, sret. apply functional_extensionality.
  intros x. destruct (b a x); auto.
Qed.

Ltac sok_do:=
  simpl;
  try rewrite do_try;
  try rewrite ret_ok';
  try rewrite do_ret.


(** * Properties of the reference implementation  *)
Lemma n_check_same:
  forall fid ms1 ms2 st,
    (n_check_compiled fid) ms1 = SOK st ms2 ->
    ms1 = ms2.
Proof.
  unfold n_check_compiled. intros fid ms1 ms2 st H. destruct ((cod ms1) # fid); inv H; auto.
Qed.

Lemma load_prog_same:
  forall fid ms1 ms2 af,
    (n_load_prog_code fid) ms1 = SOK af ms2 ->
    ms1 = ms2.
Proof.
  unfold n_load_prog_code. intros fid ms1 ms2 st H. destruct ((cod ms1) # fid); inv H; auto.
Qed.

Lemma n_install_same:
  forall fid af mut1 ac1 mut2 ac2 u,
    n_install_code fid af (mut1, ac1) = SOK u (mut2, ac2) ->
    mut1 = mut2.
Proof.
  unfold n_install_code. intros fid af mut1 ac1 mut2 ac2 u H. inv H. destruct mut1. auto.
Qed.

Lemma memset_same:
  forall x y mut ac mut1 ac1,
    n_memset x y (mut, ac) = SOK tt (mut1, ac1) ->
    ac = ac1.
Proof.
  unfold n_memset. intros x y mut ac mut1 ac1 H. inv H.
  destruct (Int.lt x mem_size); inv H1. auto.
Qed.

Lemma memget_same:
  forall x mut ac mut1 ac1 r,
    n_memget x (mut, ac) = SOK r (mut1, ac1) ->
    ac = ac1.
Proof.
  unfold n_memget. intros x mut ac mut1 ac1 r H.
  destruct (Int.lt x mem_size); inv H.
  destruct ((state_mem mut) # (pos_of_int x)); inv H1. auto.
Qed.

Lemma open_sf_same:
  forall mut ac mut2 ac2 o,
    n_open_stackframe (mut, ac) = SOK o (mut2, ac2) ->
    ac = ac2.
Proof.
  intros mut ac mut2 ac2 o H. inv H. unfold n_open_stackframe in H1. unfold sbind in H1. simpl in H1.
  destruct (state_stacktop mut); destruct (state_stack mut); inv H1; auto.
  destruct s; inv H0; auto. destruct a as [[[a b] c ] d]. inv H1. auto.
Qed.

Lemma load_same:
  forall m1 ac1 m2 ac2 i,
    n_load (m1, ac1) = SOK i (m2, ac2) ->
    ac1 = ac2.
Proof.
  intros m1 ac1 m2 ac2 i H. unfold n_load in H.
  simpl in H. destruct (state_stacktop m1); inv H. auto.
Qed.
