Add LoadPath ".".
Require Export groups.
Require Export Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.

(* Реализация группы для Z_2 *)
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

Instance semigroupBool : Semigroup bool :=
{
    mult := xorb;
    assoc := xorb_assoc
}.

Instance monoidBool : Monoid bool :=
{
  e := false;
  left_id := bool_left_id;
}.

Instance groupBool : Group bool :=
{
  inv := (@id bool);
  left_inv := bool_left_inv;
}.

(* Реализация группы для Z_3 *)
Module GroupZ_3.
(* Тип Z_3 - подмножество nat с операцией сложения по модулю 3 *)
Record Z_3 : Type := Z3
{
  n :> nat;
  proof : (n <? 3) = true
}.

(* Nat.mod_upper_bound: forall a b : nat, b <> 0 -> a mod b < b *)

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

Lemma mod_upper_bound_bool : forall (a b : nat), b <> O -> (a mod b <? b) = true.
Proof.
  intros a b H. apply (Nat.mod_upper_bound a b) in H. case Nat.ltb_spec0.
  - reflexivity.
  - intros Hcontr. contradiction.
Qed.

Check (mod_upper_bound_bool 2 3) three_ne_0.

Definition nat_Z_3 (n: nat) : Z_3 :=
  let a := n mod 3 in
  (Z3 a ((mod_upper_bound_bool n 3) three_ne_0)).

Coercion nat_Z_3: nat >-> Z_3.

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

Search (?n mod ?m < ?m ).
Definition Z_3_inv (x : Z_3) : Z_3 :=
  match x with
  | Z3 m pf => Z3 ((3 - m) mod 3) (mod_upper_bound_bool (3 - m) _ three_ne_0)
  end.

Lemma Z3_eq n m p q : n = m -> Z3 n p = Z3 m q.
Proof.
  intros H. revert p q. rewrite H. clear H. intros. apply f_equal. apply UIP_dec. apply bool_dec.
Qed.

Proposition n_apply : forall (x : nat), n (nat_Z_3 x) = x mod 3.
Proof.
  intro. simpl. reflexivity.
Qed.

Proposition n_apply' : forall (x : nat) (prf: (x <? 3) = true), n (Z3 x prf) = x.
Proof.
  intros. simpl. reflexivity.
Qed.

Proposition Z_op_sum : forall (x y: nat), Z3_op x y = x + y.
Proof.
  intros. unfold Z3_op. apply Z3_eq. repeat rewrite (n_apply _). rewrite (Nat.add_mod x y 3 three_ne_0). reflexivity.
Qed.

Proposition Z_op_sum' : forall (x y: Z_3), Z3_op x y = (n x) + (n y).
Proof.
  intros. unfold Z3_op. apply Z3_eq. repeat rewrite (n_apply _). rewrite (Nat.add_mod x y 3 three_ne_0). reflexivity.
Qed.

Example Z_3_inv_0 : Z_3_inv z3_0 = z3_0.
Proof.
  simpl. apply Z3_eq. reflexivity.
Qed.

Example Z_3_inv_1 : Z_3_inv z3_0 = z3_0.
Proof.
  simpl. apply Z3_eq. reflexivity.
Qed.

Example Z_3_inv_2 : Z_3_inv z3_2 = z3_1.
Proof.
  simpl. apply Z3_eq. reflexivity.
Qed.

(* Доказательство групповых теорем для Z_3 *)

Proposition Z3_left_id : forall x: Z_3, (Z3_op z3_0 x) = x.
Proof.
  intro. unfold Z3_op. destruct x as [vx proof]. apply Z3_eq. unfold n, z3_0. rewrite plus_O_n. apply Nat.mod_small. apply Nat.ltb_lt in proof. assumption.
Qed.

Proposition Z3_left_inv : forall x: Z_3, Z3_op (Z_3_inv x) x = z3_0.
Proof.
  intro. unfold Z3_op. unfold Z_3_inv. apply Z3_eq. destruct x as [vx proof]. repeat rewrite n_apply'. rewrite (Nat.add_mod_idemp_l _ _ _ three_ne_0). rewrite Nat.sub_add.
  - simpl. reflexivity.
  - apply Nat.ltb_lt in proof. apply Nat.lt_le_incl. assumption.
Qed.

Proposition Z3_assoc : forall x y z: Z_3, Z3_op x (Z3_op y z) = Z3_op (Z3_op x y) z.
Proof.
  intros. repeat rewrite (Z_op_sum' _ _). repeat rewrite n_apply.
  unfold nat_Z_3. apply Z3_eq. rewrite (Nat.add_mod_idemp_l _ _ _ three_ne_0). rewrite (Nat.add_mod_idemp_r _ _ _ three_ne_0). rewrite Nat.add_assoc. reflexivity.
Qed.

Instance semigroupZ3 : Semigroup Z_3 :=
{
  mult := Z3_op;
  assoc := Z3_assoc
}.

Instance monoidZ3 : Monoid Z_3 :=
{
  e := z3_0;
  left_id := Z3_left_id;
}.

Instance groupZ3 : Group Z_3 :=
{
  inv := Z_3_inv;
  left_inv := Z3_left_inv;
}.

End GroupZ_3.

Module GroupZ_n.
(* Реализация группы для Z_n *)
Variable pk : nat.
(* Нам нужно, чтобы k > 0 *)
Definition k := S pk.
(* Тип Z_n - подмножество nat с операцией сложения по модулю n *)
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

Instance semigroupZk : Semigroup Z_k :=
{
  mult := Zk_op;
  assoc := Zk_assoc
}.

Instance monoidZk : Monoid Z_k :=
{
  e := zk_0;
  left_id := Zk_left_id;
}.

Instance groupZk : Group Z_k :=
{
  inv := Z_k_inv;
  left_inv := Zk_left_inv;
}.

Print Instances Semigroup.
End GroupZ_n.
