Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

Class Group G : Type :=
{
    e : G;
    mult : G -> G -> G;
    inv : G -> G;
    left_id : forall x:G, mult e x = x;
    left_inv : forall x:G, mult (inv x) x = e;
    assoc : forall x y z:G,
        mult x (mult y z) = mult (mult x y) z
}.

Class Eq A :=
{
    eqb: A -> A -> bool;
}.

Notation "x =? y" := (eqb x y) (at level 70).

Section Group_theorems.

  Parameter G: Type.
  Context `{Hgr: Group G}.
  Infix "*" := mult (at level 40, left associativity).

(* № 24 *)
(* Вспомогательная лемма, нужна в дальнейшем *)
  Proposition left_cancel : forall x y z: G,
      x * y = x * z -> y = z.
  Proof.
    intros x y z H. assert (inv x * (x * y) = inv x * (x * z))
      as Hinvx.
    - rewrite H. reflexivity.
      (* - repeat rewrite assoc in Hinvx. rewrite left_inv in Hinvx. repeat rewrite left_id in Hinvx. assumption. *)
    - now rewrite !assoc, left_inv, !left_id in Hinvx.
  Qed.

End Group_theorems.

(*   Реализация группы для Z2   *)
Proposition bool_left_id : forall x: bool, xorb false x = x.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Proposition bool_left_inv : forall x: bool, xorb (id x) x = false.
Proof.
  destruct x; simpl; reflexivity.
Qed.

Proposition xorb_assoc : forall x y z: bool, xorb x (xorb y z) = xorb (xorb x y) z.
Proof.
  intros. destruct x; destruct y; destruct z; simpl; reflexivity.
Qed.

Instance groupBool : Group bool :=
{
  e := false;
  mult := xorb;
  inv := (@id bool);
  left_id := bool_left_id;
  left_inv := bool_left_inv;
  assoc := xorb_assoc
}.

(* Тип Z_3 - подмножество nat с операцией сложения по модулю 3 *)

Record Z_3 : Type := Z3
{
  n :> nat;
  proof : (n <? 3) = true
}.

(* Определяем обитателей типа Z_3 *)
Proposition lt_0_3 : (0 <? 3) = true.
Proof.
  simpl. reflexivity.
Qed.

Definition z3_0 : Z_3 := (Z3 0 lt_0_3).

Proposition lt_1_3 : (1 <? 3) = true.
Proof.
  reflexivity.
Qed.

Definition z3_1 : Z_3 := (Z3 1 lt_1_3).

Proposition lt_2_3 : (2 <? 3) = true.
Proof.
  reflexivity.
Qed.

Definition z3_2 : Z_3 := (Z3 2 lt_2_3).
(* Конец определения обитателей *)

Proposition three_ne_0 : 3 <> 0.
Proof.
  discriminate.
Qed.

(* Instance eqZ_3 : Eq Z_3 := *)
(* { *)
(*   eqb := fun (z1 z2 : Z_3) => *)
(*            let (n1, prf1) *)
(* }. *)

Lemma mod_upper_bound_bool : forall (a b : nat), b <> O -> (a mod b <? b) = true.
Proof.
  intros a b H. apply (Nat.mod_upper_bound a b) in H. case Nat.ltb_spec0.
  - reflexivity.
  - intros Hcontr. contradiction.
Qed.

Definition Z3_op (x y: Z_3) : Z_3 :=
  let a := (x + y) mod 3 in
  Z3 a (mod_upper_bound_bool _ 3 three_ne_0).

Lemma Z_3_inv_lemma (k: nat) : ((3 + k) <? 3 = true) -> False.
Proof.
  intro. induction k as [| k' IH].
  - simpl in H. inversion H.
  - rewrite Nat.add_succ_r in H. auto.
Qed.

Lemma void {t : Set} : False -> t.
Proof.
  intro. contradiction H.
Qed.

Definition Z_3_inv (x : Z_3) : Z_3 :=
  match x with
  | Z3 0 pf => Z3 0 pf
  | Z3 1 pf => Z3 2 lt_2_3
  | Z3 2 pf => Z3 1 lt_1_3
  | Z3 (S (S (S k))) pf => void (Z_3_inv_lemma k pf)
  end.


(* n0 : nat *)
(* proof0 : (n0 <? 3) = true *)
(* Unable to unify "(n0 <? 3) = true" with *)
(*     "(n0 mod 3 <? 3) = true". *)

(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat. *)
Hint Resolve Z3_op z3_0 : Z3.

Lemma Z3_eq n m p q : n = m -> Z3 n p = Z3 m q.
Proof.
  intros H. revert p q. rewrite H. clear H. intros. apply f_equal. apply UIP_dec. apply bool_dec.
Qed.

Proposition Z3_left_id : forall x: Z_3, (Z3_op z3_0 x) = x.
Proof.
  intro. unfold Z3_op. destruct x as [vx proof]. apply Z3_eq. unfold n, z3_0. rewrite plus_O_n. apply Nat.mod_small. apply Nat.ltb_lt in proof. assumption.
Qed.

Proposition Z3_left_inv : forall x: Z_3, Z3_op (Z_3_inv x) x = z3_0.
Proof.
  intro. destruct x as [n prf]. destruct n.
  - simpl. unfold Z3_op. simpl. reflexivity.
  - destruct n0.
    + simpl. unfold Z3_op. simpl. reflexivity.
    + destruct n0.
      * simpl. unfold Z3_op. simpl. reflexivity.
      * revert prf. rewrite (plus_n_O n0). repeat rewrite plus_n_Sm. rewrite Nat.add_comm. intro. exfalso. apply Z_3_inv_lemma in prf. apply prf.
Qed.

Proposition Z3_assoc : forall x y z: Z_3, Z3_op x (Z3_op y z) = Z3_op (Z3_op x y) z.

Instance groupZ3 : Group Z3 :=
{
  e := z3_0;
  mult := z3_op;
  inv := Z_3_inv;
  left_id := bool_left_id;
  left_inv := Z3_left_inv;
  assoc := xorb_assoc
}.