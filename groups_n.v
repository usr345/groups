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

Variable pk : nat.
Definition k := S pk.
(* Тип Z_n - подмножество nat с операцией сложения по модулю 3 *)
Record Z_k : Type := Zk
{
  n :> nat;
  proof : (n <? k) = true
}.

(* Определяем обитателей типа Z_k *)
Proposition lt_0_k : (0 <? k) = true.
Proof.
  simpl. reflexivity.
Qed.

Definition zk_0 : Z_k := (Zk 0 lt_0_k).

Proposition k_ne_0 : k <> 0.
Proof.
  discriminate.
Qed.

Lemma mod_upper_bound_bool : forall (a b : nat), b <> O -> (a mod b <? b) = true.
Proof.
  intros a b H. apply (Nat.mod_upper_bound a b) in H. case Nat.ltb_spec0.
  - reflexivity.
  - intros Hcontr. contradiction.
Qed.

Check (mod_upper_bound_bool 2 k) k_ne_0.

Definition nat_Z_k (n: nat) : Z_k :=
  let a := n mod k in
  (Zk a ((mod_upper_bound_bool n k) k_ne_0)).

Coercion nat_Z_k: nat >-> Z_k.

Definition Zk_op (x y: Z_k) : Z_k :=
  let a := (x + y) mod k in
  Zk a (mod_upper_bound_bool _ k k_ne_0).

(* Unset Printing Notations. *)
Search (0 < S _).
(* Search (S ?x + ?y = ?x + S ?y). *)
(* Nat.lt_add_pos_l: forall n m : nat, 0 < n -> m < n + m *)
Lemma Z_k_inv_lemma (m: nat) : ((k + m) <? k = true) -> False.
Proof.
  simpl. change k with (S pk). unfold Nat.ltb. simpl. destruct pk.
  - intros. discriminate H.
  -  rewrite Nat.leb_le. apply Nat.lt_nge. rewrite Nat.add_succ_comm. rewrite Nat.add_comm. apply Nat.lt_add_pos_l. apply Nat.lt_0_succ.
Qed.

Lemma void {t : Set} : False -> t.
Proof.
  intro. contradiction H.
Qed.

Definition Z_k_inv (x : Z_k) : Z_k :=
  match x with
  | Zk m pf => Zk ((k - m) mod k) (mod_upper_bound_bool (k - m) _ k_ne_0)
  end.

Lemma Zk_eq n m p q : n = m -> Zk n p = Zk m q.
Proof.
  intros H. revert p q. rewrite H. clear H. intros. apply f_equal. apply UIP_dec. apply bool_dec.
Qed.

Proposition n_apply : forall (x : nat), n (nat_Z_k x) = x mod k.
Proof.
  intro. simpl. reflexivity.
Qed.

Proposition n_apply' : forall (x : nat) (prf: (x <? k) = true), n (Zk x prf) = x.
Proof.
  intros. simpl. reflexivity.
Qed.

Proposition Z_op_sum : forall (x y: nat), Zk_op x y = x + y.
Proof.
  intros. unfold Zk_op. apply Zk_eq. repeat rewrite (n_apply _). rewrite (Nat.add_mod x y k k_ne_0). reflexivity.
Qed.

Proposition Z_op_sum' : forall (x y: Z_k), Zk_op x y = (n x) + (n y).
Proof.
  intros. unfold Zk_op. apply Zk_eq. repeat rewrite (n_apply _). rewrite (Nat.add_mod x y k k_ne_0). reflexivity.
Qed.

Lemma Z_k_inv_0 : Z_k_inv zk_0 = zk_0.
Proof.
  unfold Z_k_inv. unfold zk_0. rewrite Nat.sub_0_r. apply Zk_eq. apply (Nat.mod_same k k_ne_0).
Qed.

Proposition Zk_left_id : forall x: Z_k, (Zk_op zk_0 x) = x.
Proof.
  intro. unfold Zk_op. destruct x as [vx proof]. apply Zk_eq. unfold n, zk_0. rewrite plus_O_n. apply Nat.mod_small. apply Nat.ltb_lt in proof. assumption.
Qed.

Proposition Zk_left_inv : forall x: Z_k, Zk_op (Z_k_inv x) x = zk_0.
Proof.
  intro. unfold Zk_op. unfold Z_k_inv. apply Zk_eq. destruct x as [vx proof]. repeat rewrite n_apply'. rewrite (Nat.add_mod_idemp_l _ _ _ k_ne_0). rewrite Nat.sub_add.
  - apply (Nat.mod_same k k_ne_0).
  - apply Nat.ltb_lt in proof. apply Nat.lt_le_incl. apply proof.
Qed.

Proposition Zk_assoc : forall x y z: Z_k, Zk_op x (Zk_op y z) = Zk_op (Zk_op x y) z.
Proof.
  intros. repeat rewrite (Z_op_sum' _ _). repeat rewrite n_apply.
  unfold nat_Z_k. apply Zk_eq. rewrite (Nat.add_mod_idemp_l _ _ _ k_ne_0). rewrite (Nat.add_mod_idemp_r _ _ _ k_ne_0). rewrite Nat.add_assoc. reflexivity.
Qed.

Instance groupZk : Group Z_k :=
{
  e := zk_0;
  mult := Zk_op;
  inv := Z_k_inv;
  left_id := Zk_left_id;
  left_inv := Zk_left_inv;
  assoc := Zk_assoc
}.