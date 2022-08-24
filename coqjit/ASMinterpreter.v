(* Interpreter for ASM code *)
(* So that we can run the JIT safely, without any substitution *)
(* To be substituted with actual native execution *)
Require Import common.

Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import IR.
Require Import Errors.
Require Import monad.
Require Import Asm.
Require Import primitives.
Require Import intpos.


(** * Decidable versions of some operations *)

(** From Asm.v : Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use machine registers instead of locations. *)
(* We make here a decidable version, and proofs of equivalence with the inductive definitions *)

Definition extcall_arg_dec (rs:regset) (m:mem) (l:loc) : res val :=
  match l with
  | R r => OK (rs (preg_of r))
  | S Outgoing ofs ty =>
    let bofs := Stacklayout.fe_ofs_arg + 4 * ofs in
    match (Mem.loadv (chunk_of_type ty) m (Val.offset_ptr (rs (IR RSP)) (Ptrofs.repr bofs))) with
    | Some v => OK v
    | None => Error ((MSG "Extcall_arg: Wrong load")::nil)
    end
  | S Local _ _ =>
    Error ((MSG "Extcall_arg: wrong location")::nil)
  | S Incoming _ _ =>
    Error ((MSG "Extcall_arg: wrong location")::nil)
  end.

Lemma extcall_arg_eq:
  forall rs m l v,
    extcall_arg rs m l v <-> extcall_arg_dec rs m l = OK v.
Proof.
  intros rs m l v. split; intros H.
  - inv H; simpl; auto.
    simpl in H1. rewrite H1. auto.
  - destruct l.
    + simpl in H. inv H. constructor.
    + simpl in H. destruct sl; inv H.
      destruct (Mem.loadv (chunk_of_type ty) m (Val.offset_ptr (rs RSP) (Ptrofs.repr (fe_ofs_arg + match pos with | 0 => 0 | Zpos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0 end)))) eqn:LOAD; inv H1.
      econstructor; eauto.
Qed.    

Definition extcall_arg_pair_dec (rs:regset) (m:mem) (rp:rpair loc) : res val :=
  match rp with
  | One l => extcall_arg_dec rs m l
  | Twolong hi lo =>
    do vhi <- extcall_arg_dec rs m hi;
      do vlo <- extcall_arg_dec rs m lo;
      OK (Val.longofwords vhi vlo)
  end.

Lemma extcall_arg_pair_eq:
  forall rs m rp v,
    extcall_arg_pair rs m rp v <-> extcall_arg_pair_dec rs m rp = OK v.
Proof.
  intros rs m rp v. split; intros H.
  - inv H; simpl.
    + apply extcall_arg_eq. auto.
    + apply extcall_arg_eq in H0. apply extcall_arg_eq in H1. repeat ok_do. auto.
  - destruct rp; inv H.
    + constructor. apply extcall_arg_eq. auto.
    + repeat do_ok. constructor; apply extcall_arg_eq; auto.
Qed.

Fixpoint list_res_map {A B: Type} (f:A -> res B) (l:list A) : res (list B) :=
  match l with
  | nil => OK nil
  | x::l' =>
    do fx <- f x;
    do r <- list_res_map f l';
    OK (fx::r)
  end.

Definition extcall_arguments_dec (rs:regset) (m:mem) (sg:signature) : res (list val) :=
  list_res_map (extcall_arg_pair_dec rs m) (loc_arguments sg).

Lemma res_map_forall:
  forall A B (fdec:A -> res B) (fp: A -> B -> Prop)
    (EQ: forall a b, fp a b <-> fdec a = OK b),
  forall la lb, list_forall2 fp la lb <-> list_res_map fdec la = OK lb.
Proof.
  intros A B fdec fp EQ la lb. split; intros H.
  - induction H; simpl; auto.
    apply EQ in H. rewrite H. rewrite IHlist_forall2. simpl. auto.
  - generalize dependent lb. induction la; intros lb H; simpl; auto; inv H; try constructor.
    repeat do_ok. apply EQ in HDO. constructor; auto.
Qed.

Lemma extcall_arguments_eq:
  forall rs m sg args,
    extcall_arguments rs m sg args <-> extcall_arguments_dec rs m sg = OK args.
Proof.
  intros rs m sg args. apply res_map_forall. apply extcall_arg_pair_eq.
Qed.

(** * Interpreting Primitives  *)
(* get the first argument *)
Definition hd_res {A:Type} (l:list A) : res A :=
  match l with
  | x::_ => OK x
  | _ => Error ((MSG "Not enough arguments")::nil) (* should not happen if the code is well-typed *)
  end.

Definition hd_int (l:list val) : res int :=
  match l with
  | x::nil =>
    match x with
    | Vint i => OK i
    | Vundef => Error ((MSG "Prim: invalid Vundef")::nil)
    | _ => Error ((MSG "Prim: invalid type")::nil)
    end
  | _ => Error ((MSG "Prim: invalid arity")::nil)
  end.

Definition hd2_int (l:list val) : res (int * int) :=
  match l with
  | x::y::nil =>
    match x with
    | Vint xi =>
      match y with
      | Vint yi => OK (xi, yi)
      | _ => Error ((MSG "Prim: invalid type")::nil)
      end
    | _ => Error ((MSG "Prim: invalid type")::nil)
    end
  | _ => Error ((MSG "Prim: invalid arity")::nil)
  end.

(* Extracting the 3 arguments of Close *)
Definition three_hd_int (l:list val) : res (int * int * int) :=
  match l with
  | caller::cont_lbl::retreg::nil =>
    match (caller, cont_lbl, retreg) with
    | (Vint cr, Vint cl, Vint rr) =>
      OK (cr, cl, rr)
    | _ => Error ((MSG "Prim: invalid type")::nil)
    end
  | _ => Error ((MSG "Prim: invalid arity")::nil)
  end.


(* Deprecated: no more RetCall. Extracting the 4 arguments of RetCall *)
Definition four_hd_int (l:list val) : res (int * int * int * int) :=
  match l with
  | callee::caller::cont_lbl::retreg::nil =>
    match (callee, caller, cont_lbl, retreg) with
    | (Vint ce, Vint cr, Vint cl, Vint rr) =>
      OK (ce, cr, cl, rr)
    | _ => Error ((MSG "Prim: invalid type")::nil)
    end
  | _ => Error ((MSG "Prim: invalid arity")::nil)
  end.

Definition no_arg (l:list val) : res unit :=
  match l with
  | nil => OK tt
  | _ => Error ((MSG "Prim: invalid arity")::nil)
  end.

(* Primitives can output a trace and have a return value *)
Definition prim_return: Type := (trace * int).

Definition prim_sem_dec (name:String.string) (sg:signature) (vargs:list val) : free prim_return :=
  match (String.eqb name (EF_name EF_save)) with
  | true =>
    do arg <<- fret' (hd_int vargs);
    do _ <<- fprim(Prim_Save arg);     (* changes the JIT memory (not the CompCert one) *)
    fret (E0, Int.zero)
  | false => match (String.eqb name (EF_name EF_load)) with
  | true =>
    do _ <<- fret' (no_arg vargs);
    do retval <<- fprim(Prim_Load);
    fret (E0, retval)
  | false => match (String.eqb name (EF_name EF_memset)) with
  | true =>
    do (x,y) <<- fret' (hd2_int vargs);
    do _ <<- fprim(Prim_MemSet x y);
    fret (E0, Int.zero)
  | false => match (String.eqb name (EF_name EF_memget)) with
  | true => 
    do arg <<- fret'(hd_int vargs);
    do retval <<- fprim(Prim_MemGet arg);
    fret (E0, retval)
  | false => match (String.eqb name (EF_name EF_close)) with
  | true => 
    do (caller,cont,reg) <<- fret'(three_hd_int vargs);
    do _ <<- fprim(Prim_CloseSF caller cont reg);
    fret (E0, Int.zero)
  | false => match (String.eqb name (EF_name EF_print)) with
  | true =>
    do arg <<- fret' (hd_int vargs);
    fret (print_event arg, Int.zero)
  | false => ferror ((MSG "Unknown Primitive")::nil)
  end end end end end end.


(** * The interpreter step *)
Definition ext_prim_sem (rs:regset) (m:mem) (name:string) (sg:signature) : free (trace * state) :=
  do args <<- fret' (extcall_arguments_dec rs m sg);
    do (t, res) <<- prim_sem_dec name sg args;
    do rs' <<- fret ((set_pair (loc_external_result sg) (Vint res) (undef_caller_save_regs rs)) #PC <- (rs RA));
    fret (t, State rs' m). (* cannot change the memory *)

Definition eq_null (v:val) : bool:=
  match (Archi.ptr64, v) with
  | (true, Vlong i) => Int64.eq i Int64.zero
  | (false, Vint i) => Int.eq i Int.zero
  | _ => false
  end.
    
Definition is_final (ast:state) : option int :=
  match ast with
  | (State rs m) =>
    match (eq_null (rs PC)) with
    | true =>
      match (rs RAX) with
      | Vint r => Some r
      | _ => None
      end
    | false => None
    end
  end.

Lemma is_final_correct:
  forall s r, is_final s = Some r <-> Asm.final_state s r.
Proof.
  intros s r. unfold is_final. split; intros.
  - destruct s. destruct (eq_null (r0 PC)) eqn:NULL; inv H. destruct (r0 RAX) eqn:HRAX; inv H1.
    constructor; auto. unfold eq_null in NULL. unfold Vnullptr.
    destruct (Archi.ptr64); simpl in NULL; destruct (r0 PC); inv NULL.
    f_equal. apply Int64.same_if_eq. auto.
    f_equal. apply Int.same_if_eq. auto.
  - inv H. rewrite H0. rewrite H1. unfold eq_null. unfold Vnullptr.
    destruct (Archi.ptr64); simpl.
    rewrite Int64.eq_true. auto.
    rewrite Int.eq_true. auto.
Qed.

(* computes the return checkpoint *)
Definition get_checkpoint (i:int) : res checkpoint :=
  if (Int.eq i RETRET) then OK (C_Return nat_ret) else
    if (Int.eq i RETCALL) then OK (C_Call nat_call) else
      if (Int.eq i RETDEOPT) then OK (C_Deopt nat_deopt) else
        Error ((MSG "Invalid Checkpoint")::nil).


Definition asm_step (ge:genv) (ast:state) : free (trace * itret int state) :=
  match ast with
  | s =>
    match (is_final s) with     (* checking for final state *)
    | Some i => fret (E0, Done i)
    | None => 
    match s with
    | State rs m =>
      match (rs PC) with
      | Vptr b ofs =>
        match (Genv.find_funct_ptr ge b) with
        | Some (Internal f) =>
          match (find_instr (Ptrofs.unsigned ofs) f.(fn_code)) with
          | Some (Pbuiltin ef args res) =>
            (* Builtin step *)
            ferror ((MSG "Builtin")::nil)
          (* We don't support builtins in our semantics. the backend don't generate them for our programs anyway *)
          | Some i =>
            (* Internal Step *)
            match (exec_instr ge f i rs m) with
            | Next rs' m' => fret (E0, Halt (State rs' m'))
            | Stuck => ferror ((MSG "Stuck")::nil)
            end
          | _ => ferror ((MSG "Invalid find_instr")::nil)
          end
        | Some (External ef) =>
          match ef with
          | EF_runtime name sg =>
            match (Ptrofs.eq ofs Ptrofs.zero) with
            | true => do (t, s) <<- ext_prim_sem rs m name sg;
                       fret (t, Halt s)
            | false => ferror ((MSG "Invalid Ptr ofs")::nil)
            end
          | _ => ferror ((MSG "Invalid External Function")::nil)
                       (* we have proved that no other external calls are generated *)
          end
        | _ => ferror ((MSG "Invalid find_funct")::nil)
        end
      | Vundef => ferror ((MSG "Invalid Vundef PC")::nil)
      | Vint _ => ferror ((MSG "Invalid Vint PC")::nil)
      | Vlong _ => ferror ((MSG "Invalid Vlong PC")::nil)
      | Vfloat _ => ferror ((MSG "Invalid Vfloat PC")::nil)
      | Vsingle _ => ferror ((MSG "Invalid Vsingle PC")::nil)
      end
    end
    end
  end.


Definition asm_int_step (ge:genv) (s:Asm.state) : free (trace * synchro_state) :=
  do (t,r) <<- asm_step ge s;
    match r with
    | Halt (a) => fret (t, Halt_ASM ge a)
    | Done a =>
      do cp <<- fret' (get_checkpoint a);
        fret (t, synchro_of cp)
    end.


(* initial state for a function *)
(* Functional version of the inductive definition in Asm.v *)
Definition init_nat_state (p:program) : res Asm.state :=
  do m0 <- try_op (Genv.init_mem p) "Init mem failed";
    do ge <- OK (Genv.globalenv p);
    do rs0 <- OK ((Pregmap.init Vundef) # PC <- (Genv.symbol_address ge p.(AST.prog_main) Ptrofs.zero)
                                       # RA <- Vnullptr
                                       # RSP <- Vnullptr);
    OK (State rs0 m0).

Definition build_genv (p:program): genv :=
  Genv.globalenv p.
