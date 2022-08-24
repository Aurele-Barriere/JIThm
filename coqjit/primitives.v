(* Defining primitives that are used by the RTL and x86 code *)
(* The JIT has other primitives (see monad.v) *)

Require Import RTL.
Require Import common.
Require Import AST.
Require Import Integers.
Require Import Errors.

(* Definition prim_cc : calling_convention := *)
(*   mkcallconv false false false.  *)
(* Definition prim_cc_vararg : calling_convention := *)
(*   mkcallconv true false false. *)

Definition prim_cc (nbargs:Z) :=
  mkcallconv (Some nbargs) false false.


Inductive ext_primitive: Type :=
| EF_save : ext_primitive
| EF_load : ext_primitive
| EF_memset : ext_primitive
| EF_memget : ext_primitive
| EF_close: ext_primitive
| EF_print: ext_primitive.


Definition EF_name (ef:ext_primitive) : string :=
  match ef with
  | EF_save => "_SAVE"
  | EF_load => "_LOAD"
  | EF_memset => "_MEMSET"
  | EF_memget => "_MEMGET"
  | EF_close => "_CLOSE"
  | EF_print => "_PRINT"
  end.

(* The return type of each primitive *)
(* Since they are axiomatized as emitting a syscall event, they should all return an integer (even 0) *)
Definition EF_rettype (ef:ext_primitive) : rettype :=
  Tret Tint.

(* Arguments of each primitives *)
Definition EF_sigargs (ef:ext_primitive) : list typ :=
  match ef with
  | EF_save | EF_print | EF_memget => (Tint::nil)
  | EF_load => nil
  | EF_memset => (Tint::Tint::nil)
  | EF_close => (Tint::Tint::Tint::nil) (* RetCall (caller, cont_lbl, retreg) *)
  end.

Definition EF_nbargs (ef:ext_primitive) : Z :=
  match ef with
  | EF_save | EF_print | EF_memget => 1%Z
  | EF_load => 0%Z
  | EF_memset => 2%Z
  | EF_close => 3%Z
  end.

(* Identifiers *)
Definition EF_ident (ef:ext_primitive) : ident :=
  match ef with
  | EF_save => Pos.of_nat(400)
  | EF_load => Pos.of_nat(401)
  | EF_memset => Pos.of_nat(402)
  | EF_memget => Pos.of_nat(403)
  | EF_close => Pos.of_nat(404)
  | EF_print => Pos.of_nat(405)
  end.

Definition EF_sig (ef:ext_primitive) : signature :=
  mksignature (EF_sigargs ef) (EF_rettype ef) (prim_cc (EF_nbargs ef)).

Definition EF (ef:ext_primitive) : external_function :=
  EF_runtime (EF_name ef) (EF_sig ef).



(** * Primitive Semantics Axiomatization  *)
Require Import Events.
Require Import Values.

Definition intlistval (l:list int) : list val :=
  map Vint l.

Inductive match_typ: list int -> list typ -> Prop :=
| match_empty: match_typ nil nil
| match_cons: forall i l m,
    match_typ l m ->
    match_typ (i::l) (Tint::m).

Definition intlisteval (l: list int): list eventval :=
  map EVint l.

Definition injective {A B} (f:A->B): Prop :=
  forall x y, f x = f y -> x = y.

Lemma map_inj :
  forall A B (f:A->B),
    injective f -> injective (map f).
Proof.
  intros A B f H. unfold injective in *. intros x. induction x; intros.
  - simpl in H0. destruct y; inv H0. auto.
  - destruct y; inv H0. apply H in H2. subst. f_equal. apply IHx. auto.
Qed.

Lemma intlistval_inj:
  injective intlistval.
Proof.
  unfold intlistval. apply map_inj. unfold injective. intros x y H. inv H. auto.
Qed.

Lemma intlisteval_inj:
  injective intlisteval.
Proof.
  unfold intlisteval. apply map_inj. unfold injective. intros x y H. inv H. auto.
Qed.

Lemma lessdef_args_same:
  forall int_args sig_args val_args,
    match_typ int_args sig_args ->
    Val.lessdef_list (intlistval int_args) val_args ->
    val_args = (intlistval int_args).
Proof.
  intros int_args. induction int_args; intros; inv H0; auto.
  simpl. inv H3. f_equal. inv H. eapply IHint_args; eauto.
Qed.

Lemma inject_args_same:
  forall int_args sig_args val_args f,
    match_typ int_args sig_args ->
    Val.inject_list f (intlistval int_args) val_args ->
    val_args = (intlistval int_args).
Proof.
  intros int_args. induction int_args; intros; inv H0; auto.
  simpl. inv H3. inv H. f_equal. eapply IHint_args; eauto.
Qed.


(** * The AXIOM  *)
Axiom ext_prim_axiom:
  forall ge vargs mem t retval mem' ef,
    external_functions_sem (EF_name ef) (EF_sig ef) ge vargs mem t retval mem' <->
    exists args:list int, exists ret:int, vargs = intlistval args /\
    match_typ args (EF_sigargs ef) /\
    mem = mem' /\
    retval = Vint ret /\
    t = (Event_syscall (EF_name ef) (intlisteval args) (EVint ret))::nil.

(* This axiom adds a condition on external_functions_sem, but CompCert already includes an axiom for that semantics *)
(* In the following proof, we show that there is *)
(* no inconsistency with what's already assumed of external_functions_sem *)
(* We show that our axiom specilizes the CompCert one, and we can reprove the compCert one using only our own *)
Theorem ext_prim_properties:
  forall ef,
    extcall_properties (external_functions_sem (EF_name ef) (EF_sig ef)) (EF_sig ef).
Proof.
  intros ef. split; intros.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst. simpl. auto.
  - apply ext_prim_axiom in H0 as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst.
    apply ext_prim_axiom. exists args. exists ret. split; auto.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst. auto.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst. auto.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst. auto.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst.
    exists (Vint ret). exists m1'. split; try split; try split; auto. apply ext_prim_axiom. exists args. exists ret. split; auto.
    eapply lessdef_args_same; eauto.  apply Memory.Mem.unchanged_on_refl.
  - apply ext_prim_axiom in H0 as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst.
    exists f. exists (Vint ret). exists m1'. split; auto. apply ext_prim_axiom.
    exists args. exists ret. split; auto. eapply inject_args_same; eauto. split; auto. split; auto. split; auto.
    apply Memory.Mem.unchanged_on_refl.
    split; auto. apply Memory.Mem.unchanged_on_refl. split; auto. unfold inject_separated.
    intros b1 b2 delta H0 H3. rewrite H3 in H0. inv H0.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst. auto.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst.
    inv H0. simpl in H6. destruct res2; inv H6. exists (Vint i). exists m1.
    apply ext_prim_axiom. exists args. exists i. split; auto.
  - apply ext_prim_axiom in H as [args [ret [ARGS [MATCHA [MEM [MATCHR EVENT]]]]]]; subst.
    apply ext_prim_axiom in H0 as [args0 [ret0 [ARGS0 [MATCHA0 [MEM0 [MATCHR0 EVENT0]]]]]]; subst.
    apply intlistval_inj in ARGS0. subst. split; auto.
    + constructor; auto. constructor. constructor.
    + intros H. inv H. split; auto.
Qed.







(** * Return Identifiers  *)
(* When a RTL or x86 returns, it does so with an integer that indicates if this piece of program *)
(* either returns (and the ret value has been pushed to the buffer), calls (and the arguments + id have been pushed) *)
(* or deoptimizes (and the target has been pushed) *)

(* We define here the corresponding identifiers *)
Definition RETRET: int := Int.repr 501.
Definition RETCALL: int := Int.repr 502.
Definition RETDEOPT: int := Int.repr 503.
