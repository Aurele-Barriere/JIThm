(* State Monad *)
Require Export Coqlib.
Require Export String.
Require Export Maps.
Require Export Logic.FunctionalExtensionality.
Require Import Errors.
Require Import Asm.
Require Import Integers.
Require Import IR.
Require Import Events.
Require Import common.

(** * A simple Error Monad  *)
(* We now use the definition from lib/Errors *)
(* But we give here a few more useful definitions and tactics *)

Definition bind3 {A B C D: Type} (v: res (A * B * C)) (f: A -> B -> C -> res D) : res D :=
  bind v (fun xyz => f (fst (fst xyz)) (snd(fst xyz)) (snd(xyz))).

Definition bind4 {A B C D E: Type} (v: res (A * B * C * D)) (f: A -> B -> C -> D -> res E) : res E :=
  bind v (fun abcd => f (fst (fst (fst abcd))) (snd (fst (fst abcd))) (snd (fst abcd)) (snd abcd)).


Notation "'do' X <- A ; B" := (bind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).
(** * Missing Notations *)
Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).
Notation "'do' ( W , X , Y , Z ) <- A ; B" := (bind4 A (fun W X Y Z => B))
   (at level 200, W ident, X ident, Y ident, Z ident, A at level 100, B at level 200).

(** * Monadic Laws for the Error monad  *)
Lemma error_left_id:
  forall (X Y:Type) (x:X) (f:X -> res Y),
    bind (OK x) f = f x.
Proof.
  intros X Y x f. simpl. auto.
Qed.

Lemma error_right_id:
  forall (X:Type) (f:res X),
    bind f (fun x => OK x) = f.
Proof.
  intros X f. induction f; simpl; auto.
Qed.

Lemma error_assoc:
  forall (X Y Z:Type) (f1: res X) (f2: X -> res Y) (f3: Y -> res Z),
    bind (bind f1 f2) f3 = bind f1 (fun x => bind (f2 x) f3).
Proof.
  intros X Y Z f1 f2 f3. induction f1; simpl; auto.
Qed.


(** * Convenient functions on Error monads  *)
(* Some functions return an option. *)
(* [try_op v s] returns the corresponding [OK], or fails with [Error s] *)
Definition try_op {A:Type} (o:option A) (s:string): res A :=
  match o with
  | None => Error ((MSG s)::nil)
  | Some v => OK v
  end.

Lemma try_op_rewrite:
  forall A (e:option A) r s,
    try_op e s = OK r -> e = Some r.
Proof.
  intros A e r s H. destruct e; inv H. auto.
Qed.

(* With f a function that transforms x, return (f x) or in case of an error, x unchanged *)
Definition safe_res {A:Type} (f:A -> res A) (x:A) :=
  match f x with
  | Error _ => x
  | OK y => y
  end.

(* Tactics to reason about error monads *)
Ltac ok_do:=
  match goal with
  | [ H: ?e = OK ?v |- context[?e]] => try rewrite H; simpl
  | [ H: ?e = Some ?v |- context[try_op ?e ?m]] => try rewrite H; simpl
  end.

Ltac do_ok:=
  let HDO := fresh "HDO" in
  match goal with
  | [ H: (do V <- ?e; ?c) = OK ?r |- _ ] => try destruct e eqn:HDO; simpl in H; inv H
  | [ H: (do (A,B) <- ?e; ?c) = OK ?r |- _ ] => try destruct e eqn:HDO; simpl in H; inv H
  | [ H: (do (A,B,C) <- ?e; ?c) = OK ?r |- _ ] => try destruct e eqn:HDO; simpl in H; inv H
  | [ H: try_op ?e ?m = OK ?r |- _ ] => try destruct e eqn:HDO; simpl in H; inv H
  end.

(* Tactics to reason about options *)
Ltac match_some:=
  match goal with
  | [ H: ?e = Some ?i,
      H1: ?e = Some ?ii |- _ ] =>
    try (rewrite H in H1; inv H1)
  end.

Ltac match_ok:=
  match goal with
  | [H: OK ?a = OK ?b |- _ ] =>
    assert(HMATCHOK: a = b) by (inv H; auto); clear H; rename HMATCHOK into H
  end.

(** * Free Monad  *)
(* We now define free monads: terminating program that call abstract primitives *)
(* First we need to define the interface of possible primitives *)
(* And for that we need to define some common types *)


(* To write terminating computations using primitives but without specifying their implementation yet *)
Inductive open_sf : Type :=
| ir_sf: IR_stackframe -> open_sf
| nat_sf: int -> int -> int -> open_sf
| empty_stack : open_sf.

(* The type of a function in ASM *)
(* This is actually several programs; one for calling the function, *)
(* and one for each continuation, indexed by the original call label *)
Definition asm_fun : Type := Asm.program * PTree.t Asm.program.

Inductive compiled_status: Type :=
| Installed: asm_fun -> compiled_status
| Not_compiled : compiled_status.

(* How the asm programs are indexed *)
(* Either indexed by a fun_id for the beginning of the function *)
(* Or by a fun_id and an original label for continuations *)
Inductive asm_id : Type :=
| Call_id: fun_id -> asm_id
| Cont_id: fun_id -> label -> asm_id.

Definition asm_get (af:asm_fun) (id:cont_id) :=
  match id with
  | Main => Some (fst af)
  | Cont p => PTree.get p (snd af)
  end.

(* List of possible primitives for the JIT *)
Inductive primitive: Type -> Type :=
| Prim_Save: int -> primitive unit
| Prim_Load: primitive int
| Prim_MemSet: int -> int -> primitive unit
| Prim_MemGet: int -> primitive int
| Prim_CloseSF: int -> int -> int -> primitive unit (* caller, cont_lbl, retreg *)
| Prim_OpenSF: primitive open_sf
| Prim_PushIRSF: IR_stackframe -> primitive unit
| Prim_Install_Code: fun_id -> asm_fun -> primitive unit
| Prim_Load_Code: asm_id -> primitive Asm.program
| Prim_Check_Compiled: fun_id -> primitive compiled_status.

(* Free Monads *)
Inductive free (T :Type) : Type :=
| pure (x : T) : free T
| impure {R} (prim : primitive R) (cont : R -> free T) : free T
| ferror (e : errmsg) : free T.
Arguments pure [T] (x).
Arguments impure [T R] (prim cont).
Arguments ferror [T] (e).

(* Bind over free monads *)
Fixpoint fbind {X Y} (f: free X) (g: X -> free Y) : free Y :=
  match f with
  | pure x => g x
  | impure prim cont =>
    impure prim (fun x => fbind (cont x) g)
  | ferror e =>
    ferror e
  end.

Definition fret {X:Type} (x:X) : free X :=
  pure x.

Definition fprim {R:Type} (p:primitive R) : free R :=
  impure p fret. 

(** * Monadic Laws for the Free Monad *)
Lemma free_left_id:
  forall (X Y:Type) (x:X) (f:X -> free Y),
    fbind (fret x) f = f x.
Proof.
  intros X Y x f. simpl. auto.
Qed.

Lemma free_right_id:
  forall (X:Type) (f:free X),
    fbind f fret = f.
Proof.
  intros X f. induction f; simpl; auto.
  f_equal. apply functional_extensionality. auto.
Qed.

Lemma free_assoc:
  forall (X Y Z:Type) (f1: free X) (f2: X -> free Y) (f3: Y -> free Z),
    fbind (fbind f1 f2) f3 = fbind f1 (fun x => fbind (f2 x) f3).
Proof.
  intros X Y Z f1 f2 f3. induction f1; simpl; auto.
  f_equal. apply functional_extensionality. intros x. rewrite H. auto.
Qed.



(** * Symbolic Monads Manipulation  *)
Definition fbind2 {A B C: Type} (f: free (A * B)) (g: A -> B -> free C) : free C :=
  fbind f (fun xy => g (fst xy) (snd xy)).

Definition fbind3 {A B C D: Type} (v: free (A * B * C)) (f: A -> B -> C -> free D) : free D :=
  fbind v (fun xyz => f (fst (fst xyz)) (snd(fst xyz)) (snd(xyz))).

Definition fbind4 {A B C D E: Type} (v: free (A * B * C * D)) (f: A -> B -> C -> D -> free E) : free E :=
  fbind v (fun abcd => f (fst (fst (fst abcd))) (snd (fst (fst abcd))) (snd (fst abcd)) (snd abcd)).

Notation "'do' X <<- A ; B" := (fbind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X , Y ) <<- A ; B" := (fbind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200).
Notation "'do' ( X , Y , Z ) <<- A ; B" := (fbind3 A (fun X Y Z => B))
   (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200).
Notation "'do' ( W , X , Y , Z ) <<- A ; B" := (fbind4 A (fun W X Y Z => B))
   (at level 200, W ident, X ident, Y ident, Z ident, A at level 100, B at level 200).

Definition nothing : free unit :=
  fret tt.


(** * Interaction between Error Monad and State Monad  *)
Definition fret' {A: Type} (x: res A) : free A :=
  match x with
  | OK a => fret a
  | Error s => ferror s
  end.

(** * Convenient try  *)
Definition try_option {A: Type} (o: option A) (e:string) : free A :=
    match o with
    | None => ferror ((MSG e)::nil)
    | Some v => fret v
    end.


(** * Non-Atomic State Machines (NASM)  *)
(* the return type of such a program *)
(* either an atomic computation, or running native code *)
Inductive nasm {State Trace:Type}: Type :=
| Ato: free (Trace * State) -> nasm
| LoadAndRun: nasm.

(* the programs (like the JIT) that can be defined with a NASM *)
Definition nasm_prog (state:Type) :Type := state -> @nasm state trace.
