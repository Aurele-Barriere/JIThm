(* Converting Integers to Positive, and Vice-Versa *)
(* This is needed because identifiers from the language (function names, continuations) *)
(* must be communicated accross languages *)

Require Import Integers.
Require Import Coqlib.
Require Import monad.
Require Import Errors.
Require Import Int.
Require Import common.
(* Require Import monad_impl. *)

Definition pos_of_int (i:int) : positive :=
  Z.to_pos (Int.intval i).

(* This fails if the positive is too big *)
(* This will prevent the backend optimization from happening *)
Definition int_of_pos (p:positive) : res int :=
  do z <- OK(Zpos p);
    match (Z.ltb z Int.modulus) with
    | true => OK (Int.repr z)
    | false => Error ((MSG "Overflowed Int/Pos conversion")::nil)
    end.


Definition nat_of_int (i:int) : nat :=
  Z.to_nat (Int.intval i).

Definition int_of_nat (n:nat) : res int :=
  let z := Z.of_nat n in
  match (Z.ltb z Int.modulus) with
  | true => OK (Int.repr z)
  | false => Error ((MSG "Overflowed Nat/Pos conversion")::nil)
  end.

Transparent Int.repr.
Lemma repr_lt:
  forall z:Z,
    Z.lt z Int.modulus ->
    Z.lt (-1 ) z ->
    Int.intval (Int.repr z) = z.
Proof.
  intros z LT POS. unfold Int.repr. simpl. rewrite Int.Z_mod_modulus_eq.
  apply Z.mod_small. split; lia.
Qed.
  
Theorem int_pos_correct:
  forall p i,
    int_of_pos p = OK i ->
    pos_of_int i = p.
Proof.
  unfold int_of_pos, pos_of_int. intros p i H. repeat do_ok. inv HDO.
  destruct (Z.ltb (Zpos p) Int.modulus) eqn:MOD; inv H1.
  rewrite repr_lt. auto.
  - rewrite Z.ltb_lt in MOD. auto.
  - assert (N: 0 <= Z.pos p) by apply Pos2Z.is_nonneg.
    rewrite <- Z.lt_pred_le in N. simpl in N. apply N.
Qed.

Theorem int_nat_correct:
  forall n i,
    int_of_nat n = OK i ->
    nat_of_int i = n.
Proof.
  unfold int_of_nat, nat_of_int. intros n i H.
  destruct (Z.ltb (Z.of_nat n) Int.modulus) eqn:MOD; inv H.
  rewrite repr_lt.
  - apply Nat2Z.id.
  - rewrite Z.ltb_lt in MOD. auto.
  - assert (N: 0 <= Z.of_nat n) by apply Nat2Z.is_nonneg.
    rewrite <- Z.lt_pred_le in N. simpl in N. apply N.
Qed.

Lemma z_mod_same:
  forall p,
    Z.pos p <? Int.modulus = true <->
    Int.Z_mod_modulus (Z.pos p) = Z.pos p.
Proof.
  intros p. split; intros H.
  - rewrite Int.Z_mod_modulus_eq. apply Zmod_small. split. apply Pos2Z.is_nonneg. apply Z.ltb_lt. auto.
  - rewrite Int.Z_mod_modulus_eq in H. apply Z.ltb_lt.
    assert (0 <= Z.pos p mod Int.modulus < Int.modulus).
    { apply Z_mod_lt. apply Int.modulus_pos. } destruct H0.
    rewrite H in H1. auto.
Qed.

Lemma ok_same:
  forall A a1 a2,
    @OK A a1 = @OK A a2 -> a1 = a2.
Proof.
  intros A a1 a2 H. inv H. auto.
Qed.

Lemma repr_same:
  forall i1 i2,
    Int.repr i1 = Int.repr i2 ->
    Int.Z_mod_modulus i1 = Int.Z_mod_modulus i2.
Proof.
  intros i1 i2 H. inv H. auto.
Qed.

Lemma pos_ok:
  forall p i,
    int_of_pos p = OK i ->
    Z.pos p <? Int.modulus = true.
Proof.
  unfold int_of_pos. intros. repeat do_ok. inv HDO.
  destruct (Z.ltb (Zpos p) Int.modulus) eqn:MOD; inv H1. auto.
Qed.
(* in this lemma, if I intro before the unfold, Qed doesnt finish... *)


Lemma same_pos:
  forall p1 p2 i,
    int_of_pos p1 = OK i ->
    int_of_pos p2 = OK i ->
    Int.repr (Zpos p1) = Int.repr (Zpos p2).
Proof.
  unfold int_of_pos. intros. repeat do_ok. inv HDO0. inv HDO.
  destruct (Z.pos p1 <? Int.modulus). 2: inv H1.
  destruct (Z.pos p2 <? Int.modulus). 2: inv H2.
  apply ok_same in H2. apply ok_same in H1. subst. auto.
Qed.

Theorem int_of_pos_injective:
  forall (p1 p2:positive) (i:int),
    int_of_pos p1 = OK i ->
    int_of_pos p2 = OK i ->
    p1 = p2.
Proof.
  intros p1 p2 i H H0.
  specialize (same_pos p1 p2 i H H0). intros.
  apply repr_same in H1. apply pos_ok in H. apply pos_ok in H0.
  apply z_mod_same in H. apply z_mod_same in H0.
  rewrite H in H1. rewrite H0 in H1. inv H1. auto.
Qed.
(* I had to do this proof in such a convoluted way because Qed would not terminate... *)
(* I have to investigate what's happening *)
