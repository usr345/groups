Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import PeanoNat.

(* Носитель группы *)
Parameter G : Type.
Parameter e : G.
Parameter inv : G -> G.
Parameter mult : G -> G -> G.
Infix "*" := mult (at level 40, left associativity).

Axiom left_id : forall x:G, e * x = x.
Axiom left_inv : forall x:G, (inv x) * x = e.
Axiom assoc : forall x y z:G,
    x * (y * z) = (x * y) * z.

(* № 24 *)
(* Вспомогательная лемма, нужна в дальнейшем *)
Proposition left_cancel : forall x y z:G,
    x * y = x * z -> y = z.
Proof.
  intros x y z H.  assert (inv x * (x * y) = inv x * (x * z))
    as Hinvx.
  - rewrite H. reflexivity.
  - repeat rewrite assoc in Hinvx. rewrite left_inv in Hinvx. repeat rewrite left_id in Hinvx. assumption.
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

Proposition inv_involution : forall x:G, inv (inv x) = x.
Proof.
  intro. apply right_inv_unique. apply left_inv.
Qed.

Proposition inv_prod : forall x y:G, inv (x*y) = inv y * inv x.
Proof.
  intros x y. apply right_inv_unique. rewrite assoc. rewrite <- assoc with (z := inv y). rewrite right_inv. rewrite right_id. rewrite right_inv. reflexivity.
Qed.

Proposition e_inv : (inv e) = e.
Proof.
  rewrite <- left_inv with (x:=e) at 2. rewrite right_id. reflexivity.
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

Proposition left_cancel_alt_proof : forall x y z:G,
    x * y = x * z -> y = z.
Proof.
  intros x y z H.
  (* Здесь самое интересное: по сути это умножение гипотезы слева на inv x *)
  apply f_equal with (f := fun g:G => inv x * g) in H. repeat rewrite assoc in H. repeat rewrite left_inv in H. repeat rewrite left_id in H. assumption.
Qed.

Proposition right_cancel : forall x y z:G, x * z = y * z -> x = y.
Proof.
  intros x y z H. apply f_equal with (f := fun g:G => g * inv z) in H. repeat rewrite <- assoc in H. repeat rewrite right_inv in H. repeat rewrite right_id in H. assumption.
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

(* № 23 - состоит из 2-х теорем *)
Proposition extra1 : forall (a: G) (lst: list G), fold_left mult lst a = mult a (fold_left mult lst e).
Proof.
  intros a lst. revert a. induction lst as [| a' lst' IH].
  - intros a. simpl. rewrite right_id. reflexivity.
  - intros a. simpl. rewrite left_id. rewrite IH. rewrite (IH a'). rewrite assoc. reflexivity.
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

Fixpoint pow (a: G) (n: nat) {struct n} : G :=
  match n with
  | 0 => e
  | S n' => a * (pow a n')
  end.

(* № 27 *)
Proposition a_pow_m_n : forall (a: G) (n m: nat), (pow a n)*(pow a m) = pow  a (n + m).
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

Proposition a_pow_comm : forall (a: G) (n m: nat), commutes_with (pow a n) (pow a m).
Proof.
  intros. unfold commutes_with. repeat rewrite a_pow_m_n. rewrite Nat.add_comm. reflexivity.
Qed.
