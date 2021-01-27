Require Import ZArith.
Add LoadPath ".".
Require Import groups.
Instance semigroupZ : Semigroup Z :=
{
  mult := Z.add;
  assoc := Z.add_assoc;
}.

Instance monoidZ : Monoid Z :=
{
  e := 0;
  left_id := Z.add_0_l;
}.

Instance groupZ : Group Z :=
{
  inv := Z.opp;
  left_inv := Z.add_opp_diag_l;
}.

Open Scope group_scope.
Section Z_Groups.
  Variable G: Type.
  Context `{Hgr: Group G}.

  Definition pow_z (a: G) (z: Z) : G :=
    match z with
    | Z0 => e
    | Zpos x => pow G a (Pos.to_nat x)
    | Zneg x => inv (pow G a (Pos.to_nat x))
    end.

  Notation "a ** b" := (pow_z a b) (at level 35, right associativity).

  Lemma pow_a_n_plus_1_Z : forall (a: G) (n: Z), (pow_z a (Z.succ n)) = a * pow_z a n.
  Proof.
    intros a n. unfold Z.succ. unfold Z.add.
    destruct n.
    - simpl. reflexivity.
    - simpl. rewrite (Pos2Nat.inj_add p 1). rewrite Nat.add_comm. rewrite <- a_pow_m_n. simpl. rewrite (right_id G). reflexivity.
    - rewrite <- Pos2Z.add_pos_neg. induction p using Pos.peano_ind.
      + simpl. rewrite (right_id G). rewrite right_inv. reflexivity.
      + rewrite <- Pos.add_1_l. rewrite <- Pos2Z.add_neg_neg. rewrite Z.add_assoc. rewrite Z.add_opp_diag_r. rewrite Z.add_0_l. rewrite Pos2Z.add_neg_neg. unfold pow_z. rewrite Pos.add_comm. rewrite Pos2Nat.inj_add. simpl. rewrite <- a_pow_m_n. rewrite inv_prod. simpl. rewrite (right_id G). rewrite assoc. rewrite right_inv. rewrite left_id. reflexivity.
  Qed.

  Lemma pow_a_n_minus_1_Z : forall (a: G) (n: Z), (pow_z a (Z.pred n)) = inv(a) * pow_z a n.
  Proof.
    intros a n. unfold Z.pred. unfold Z.add.
    destruct n.
    - simpl. repeat rewrite (right_id G). reflexivity.
    - rewrite <- Pos2Z.add_pos_neg. induction p using Pos.peano_ind.
      + simpl. rewrite (right_id G). rewrite left_inv. reflexivity.
      + rewrite Pplus_one_succ_l. rewrite Pos.add_1_l. rewrite Pos2Z.inj_succ. rewrite pow_a_n_plus_1_Z. rewrite assoc. rewrite left_inv. rewrite left_id. rewrite <- Z.add_1_r. rewrite <- Z.add_assoc. rewrite Pos2Z.add_pos_neg. simpl (Z.pos_sub 1 1). rewrite Z.add_0_r. reflexivity.
    - simpl. rewrite (Pos2Nat.inj_add p 1). rewrite <- a_pow_m_n. rewrite inv_prod. simpl (pow G a (Pos.to_nat 1)). rewrite (right_id G). reflexivity.
  Qed.

  Proposition a_pow_m_n_Z : forall (a: G) (n m: Z), (pow_z a n)*(pow_z a m) = pow_z a (n + m).
  Proof.
    intros. induction n using Z.peano_ind.
    - simpl. apply left_id.
    - rewrite pow_a_n_plus_1_Z. rewrite <- assoc. rewrite IHn. rewrite <- pow_a_n_plus_1_Z. rewrite Z.add_succ_l. reflexivity.
    - rewrite pow_a_n_minus_1_Z. rewrite <- assoc. rewrite IHn.
      rewrite Z.add_pred_l. rewrite pow_a_n_minus_1_Z. reflexivity.
  Qed.

  Definition order (a: G) (n: nat) :=
    pow G a n = e /\ (forall k, 0 < k < n -> pow G a k <> e).

End Z_Groups.
Close Scope group_scope.
