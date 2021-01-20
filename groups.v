Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import PeanoNat.
Require Import ZArith.
(* G - носитель группы *)
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
  (* Пусть a, b — произвольные элементы некоторой группы G. *)
  (* Доказать, что каждое из уравнений ax = b и ya = b *)
  (* имеет, и притом ровно одно, решение в данной группе. *)
  (* Условие единственности можно выразить *)
  (* следующим образом: если a*b1 = a*b2 или b1*a = b2*a, то *)
  (* b1 = b2. *)
  Proposition left_cancel : forall x y z:G,
      x * y = x * z -> y = z.
  Proof.
    intros x y z H.  assert (inv x * (x * y) = inv x * (x * z))
      as Hinvx.
    - rewrite H. reflexivity.
    - repeat rewrite assoc in Hinvx. rewrite left_inv in Hinvx. repeat rewrite left_id in Hinvx. assumption.
  Qed.

  Proposition left_cancel_alt_proof : forall x y z:G,
      x * y = x * z -> y = z.
  Proof.
    intros x y z H.
    (* Здесь самое интересное: по сути это умножение гипотезы слева на inv x *)
    apply f_equal with (f := fun g:G => inv x * g) in H. repeat rewrite assoc in H. repeat rewrite left_inv in H. repeat rewrite left_id in H. assumption.
  Qed.

  Proposition right_id : forall x:G, x * e = x.
  Proof.
    intro. apply left_cancel with (x := inv x). rewrite assoc. repeat rewrite left_inv. rewrite left_id. reflexivity.
  Qed.

  Proposition right_inv:
    forall x:G, x * inv x = e.
  Proof.
    intro. apply left_cancel with (x := inv x). rewrite assoc.
    rewrite left_inv. rewrite left_id. rewrite right_id. reflexivity.
  Qed.

  Proposition right_inv_unique: forall x y:G, x * y = e -> inv x = y.
  Proof.
    intros x y H. apply left_cancel with (x := x). transitivity e.
    - apply right_inv.
    - symmetry. assumption.
  Qed.

  (* № 20.1 Доказать, что e^{−1} = e. *)
  Proposition e_inv : (inv e) = e.
  Proof.
    rewrite <- left_inv with (x:=e) at 2. rewrite right_id. reflexivity.
  Qed.

  (* № 20.2 Доказать, что (a^{−1})^{−1} = a. *)
  Proposition inv_involution : forall x:G, inv (inv x) = x.
  Proof.
    intro. apply right_inv_unique. apply left_inv.
  Qed.

  (* № 23.1 Доказать, что в произвольной группе: *)
  (* 1) (a*b)^{−1} = b^{−1} * a^{−1} *)
  Proposition inv_prod : forall x y:G, inv (x*y) = inv y * inv x.
  Proof.
    intros x y. apply right_inv_unique. rewrite assoc. rewrite <- assoc with (z := inv y). rewrite right_inv. rewrite right_id. rewrite right_inv. reflexivity.
  Qed.

  (* № 23.2 Доказать, что в произвольной группе: *)
  (* (a_1 * (a_2 * a_3) * ... a_n * a) = a * (a_1 * a_2 * a_3 * ... * e) *)
  Proposition extra1 : forall (a: G) (lst: list G), fold_left mult lst a = mult a (fold_left mult lst e).
  Proof.
    intros a lst. revert a. induction lst as [| a' lst' IH].
    - intros a. simpl. rewrite right_id. reflexivity.
    - intros a. simpl. rewrite left_id. rewrite IH. rewrite (IH a'). rewrite assoc. reflexivity.
  Qed.

  Definition commutator : G -> G -> G :=
    fun x y:G => x * y * inv x * inv y.

  Notation "[ x , y ]" := (commutator x y).

  Proposition commutator_inv : forall x y:G, inv [x, y] = [y, x].
  Proof.
    intros. unfold commutator. repeat rewrite inv_prod. repeat rewrite inv_involution. repeat rewrite assoc. reflexivity.
  Qed.

  Definition commutes_with : G -> G -> Prop :=
    fun x y:G => x * y = y * x.

  Proposition product_commutes :
    forall x y z:G, commutes_with x z -> commutes_with y z ->
               commutes_with (x * y) z.
  Proof.
    intros x y z Hxz Hyz. red. rewrite <- assoc. rewrite Hyz. rewrite assoc. rewrite Hxz. rewrite <- assoc. reflexivity.
  Qed.

  (* № 24.2 *)
  Proposition right_cancel : forall x y z:G, x * z = y * z -> x = y.
  Proof.
    intros x y z H. apply f_equal with (f := fun g:G => g * inv z) in H. repeat rewrite <- assoc in H. repeat rewrite right_inv in H. repeat rewrite right_id in H. assumption.
  Qed.

  (* № 19 Доказать, что для любого элемента a группы суще-
ствует единственный обратный элемент inv a. *)
  Proposition left_inv_unique: forall y: G, exists x: G, (x * y = e /\ forall x':G, x'*y = e -> x = x').
  Proof.
    intros y. exists (inv y). split.
    - apply left_inv.
    (* left_cancel : forall x y z:G, *)
    (* x * y = x * z -> y = z. *)
    - intros x' H. rewrite <- (left_inv y) in H. apply right_cancel in H. rewrite H. reflexivity.
  Qed.

  Proposition commutator_e_impl_commutes : forall x y:G, [x, y] = e -> commutes_with x y.
  Proof.
    intros x y H. red. unfold commutator in H. rewrite <- right_inv with (x:=y) in H. apply f_equal with (f := fun g:G => g * y) in H. rewrite <- assoc in H. rewrite left_inv in H. rewrite right_id in H.  rewrite <- (assoc y _ _) in H. rewrite left_inv in H. rewrite <- right_inv with (x:=x) in H. apply f_equal with (f := fun g:G => g * x) in H. rewrite <- assoc in H. rewrite left_inv in H. rewrite right_id in H. rewrite assoc in H. rewrite <- (assoc _ x _) in H. rewrite right_inv in H. rewrite right_id in H. assumption.
  Qed.

  Proposition commutes_impl_commutator_e : forall x y:G, commutes_with x y -> [x, y] = e.
  Proof.
    intros x y H. unfold commutator. red in H. apply f_equal with (f := fun g:G => g * inv x) in H. rewrite <- (assoc _ x _) in H. rewrite right_inv in H. rewrite right_id in H. apply f_equal with (f := fun g:G => g * inv y) in H. rewrite right_inv in H. assumption.
  Qed.

  (* Сопряжение, соединение *)
  Definition conjugation (x y: G) : G :=
    inv y * x * y.

  Notation "x ^ y" := (conjugation x y).

  Proposition xy_conj_e : forall x y z:G, (x^z) * (y^z)  = (x*y)^z.
  Proof.
    intros. unfold conjugation. rewrite <- (assoc (inv z) y z). rewrite (assoc (inv z * x * z) (inv z) (y * z)). rewrite <- (assoc ((inv z) * x) z (inv z)). rewrite right_inv. rewrite right_id. repeat rewrite assoc. reflexivity.
  Qed.

  Proposition e_conj_y_eq_e : forall x:G, e^x = e.
  Proof.
    intro. unfold conjugation. rewrite <- assoc. rewrite left_id. apply left_inv.
  Qed.

  Proposition x_conj_e_eq_x : forall x:G, x^e = x.
  Proof.
    intro. unfold conjugation. rewrite e_inv. rewrite left_id. rewrite right_id. reflexivity.
  Qed.

  Proposition x_min1 : forall x y:G, (inv x)^y = inv (x^y).
  Proof.
    intros. unfold conjugation. repeat rewrite inv_prod. rewrite inv_involution. rewrite assoc. reflexivity.
  Qed.

  Proposition x_y_z : forall x y z:G, (x^y)^z = x^(y*z).
  Proof.
    intros. unfold conjugation. rewrite inv_prod. repeat rewrite assoc. reflexivity.
  Qed.

  Proposition fold_unfold : forall lst: list G, inv (fold_left mult lst e) = fold_left mult (map inv (rev lst)) e.
  Proof.
    intro. induction lst as [| a lst' IH'].
    - simpl. apply e_inv.
    - simpl. rewrite left_id. rewrite extra1. rewrite inv_prod. rewrite IH'. rewrite map_app. simpl. rewrite fold_left_app. simpl. reflexivity.
  Qed.

  (* № 25 *)
  Proposition aa_e_commutative : forall a b: G, (forall x : G, x * x = e) -> commutes_with a b.
  Proof.
    intros a b He. specialize (He a) as Ha. specialize (He b) as Hb. rewrite <- Hb in Ha. apply f_equal with (f := fun g:G => b * g * b) in Ha. repeat rewrite assoc in Ha. rewrite <- (assoc (b*a) a b) in Ha. rewrite <- (assoc (b*b) b b) in Ha. rewrite Hb in Ha. rewrite left_id in Ha.
    specialize (He (a*b)) as Hab. rewrite <- Hab in Ha. apply f_equal with (f := fun g:G => g * (inv (a*b))) in Ha. rewrite <- (assoc (b*a) (a*b) (inv (a*b))) in Ha. rewrite <- (assoc (a*b) (a*b) (inv (a*b))) in Ha. rewrite right_inv in Ha. repeat rewrite right_id in Ha. unfold commutes_with. symmetry in Ha. assumption.
  Qed.

  Lemma aa_e_commutative' : (forall x : G, x * x = e) -> (forall x : G, x = inv x).
  Proof.
    intros. specialize (H x) as Hx. rewrite <- (left_inv x) in Hx. apply (right_cancel x (inv x) x) in Hx. assumption.
  Qed.

  Lemma aa_e_commutative'' : forall a b: G, (forall x : G, x * x = e) -> commutes_with a b.
  Proof.
    intros. unfold commutes_with. rewrite (aa_e_commutative' H a) at 2. rewrite (aa_e_commutative' H b) at 2. rewrite <- inv_prod. rewrite <- (aa_e_commutative' H (a*b)). reflexivity.
  Qed.

  Fixpoint pow (a: G) (n: nat) {struct n} : G :=
    match n with
    | 0 => e
    | S n' => a * (pow a n')
    end.

  Notation "a ** b" := (pow a b) (at level 35, right associativity).

  (* № 27 *)
  Proposition a_pow_m_n : forall (a: G) (n m: nat), (pow a n)*(pow a m) = pow a (n + m).
  Proof.
    intros. induction n as [| n' IH] ; simpl.
    - rewrite left_id. reflexivity.
    - rewrite <- IH. rewrite assoc. reflexivity.
  Qed.

  (* № 26 *)
  Proposition a_pow_m : forall (a: G) (n: nat), inv (pow a n) = pow (inv a) n.
  Proof.
    intros. apply right_cancel with (z := (pow a n)). rewrite left_inv. symmetry. induction n as [| n' IHn'].
    - simpl. apply left_id.
    - rewrite <- Nat.add_1_r at 1. rewrite <- (a_pow_m_n (inv a) n' 1). simpl. rewrite right_id. rewrite assoc. rewrite <- (assoc (pow (inv a) n') (inv a) a). rewrite left_inv. rewrite right_id. assumption.
  Qed.

  Proposition e_pow_n_eq_e : forall (n: nat), (pow e n) = e.
  Proof.
    intros. induction n as [| n' IH] ; simpl; try reflexivity.
    rewrite left_id. apply IH.
  Qed.

  (* № 28 *)
  Proposition theo_28 : forall (a: G) (n m: nat), (pow (pow a n) m) = pow a (n * m).
  Proof.
    intros. induction m as [| m' IH] ; simpl.
    - rewrite <- mult_n_O. simpl. reflexivity.
    - rewrite IH. rewrite Nat.mul_succ_r. rewrite Nat.add_comm. rewrite <- a_pow_m_n. reflexivity.
  Qed.

  Proposition a_pow_comm : forall (a: G) (n m: nat), commutes_with (pow a n) (pow a m).
  Proof.
    intros. unfold commutes_with. repeat rewrite a_pow_m_n. rewrite Nat.add_comm. reflexivity.
  Qed.

  (* Произведение всех элементов списка *)
  Fixpoint prod (lst : list G) :=
    match lst with
    | nil => e
    | h :: t => h * (prod t)
    end.

  (* Proposition concat : forall (lst1 lst2 : list G), prod lst1 * prod lst2 = prod (lst1 ++ lst2). *)
  (* Proof. *)
  (*   intros. *)

  Definition order a n :=
    a ** n = e /\ (forall k, 0 < k < n -> a ** k <> e).

  (* Set Printing All. *)
  (* Proposition pow_i_neq_poq_j: *)
  (*   forall i j a n, order a n ->  i < j < n -> *)
  (*              pow a i <> pow a j. *)

  (*   forall (i, j: nat) (a: G) (n: nat), order a n ->  i < j < n -> *)
  (*              pow a i <> pow a j. *)
  (*   Proof. *)
  (*     intro. *)

  Definition pow_z (a: G) (z: Z) : G :=
    match z with
    | Z0 => e
    | Zpos x => pow a (Pos.to_nat x)
    | Zneg x => inv (pow a (Pos.to_nat x))
    end.

  Search (Pos.to_nat (?a + ?b) = Pos.to_nat ?a + Pos.to_nat ?b).
  (* Pos.to_nat *)
  (* Pos2Nat.inj_add: forall p q : positive, Pos.to_nat (p + q) = Pos.to_nat p + Pos.to_nat q *)
  (* Proposition lemma1 : forall () zpow a (Z.pos_sub p p0) = (pow a p) * inv (pow a p0). *)
    (* Search Pos_to_nat. *)
  (* Proposition a_pow_m_n : forall (a: G) (n m: nat), (pow a n)*(pow a m) = pow a (n + m). *)
  Lemma pow_a_n_plus_1_pos : forall (a: G) (n: positive), pow_z a (Z.succ (Zpos n)) = a * pow_z a (Zpos n).
  Proof.
    intros a n. simpl. rewrite (Pos2Nat.inj_add n 1). rewrite Nat.add_comm. rewrite <- a_pow_m_n. simpl. rewrite right_id. reflexivity.
  Qed.

  Locate "-".
  Search ((1 + _)%positive).
  Search (Z.neg (_ + _)).
  Lemma pow_a_n_plus_1_Z : forall (a: G) (n: Z), (pow_z a (Z.succ n)) = a * pow_z a n.
  Proof.
    intros a n. unfold Z.succ. unfold Z.add.
    destruct n.
    - simpl. reflexivity.
    - apply pow_a_n_plus_1_pos.
    - rewrite <- Pos2Z.add_pos_neg. induction p using Pos.peano_ind.
      + simpl. rewrite right_id. rewrite right_inv. reflexivity.
      + rewrite <- Pos.add_1_l. rewrite <- Pos2Z.add_neg_neg. rewrite Z.add_assoc. rewrite Z.add_opp_diag_r. rewrite Z.add_0_l. rewrite Pos2Z.add_neg_neg. unfold pow_z. rewrite Pos.add_comm. rewrite Pos2Nat.inj_add. simpl. rewrite <- a_pow_m_n. rewrite inv_prod. simpl. rewrite right_id. rewrite assoc. rewrite right_inv. rewrite left_id. reflexivity.
  Qed.

  Proposition a_pow_m_n_Z : forall (a: G) (n m: Z), (pow_z a n)*(pow_z a m) = pow_z a (n + m).
  Proof.
    intros. induction n using Z.peano_ind.
    - simpl. apply left_id.
    - unfold Z.succ.
    induction n as [| n' IH | n' IH].
    -
    - simpl. destruct m.
      + simpl. apply right_id.
      +

End Group_theorems.
