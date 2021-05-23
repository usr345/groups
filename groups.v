Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import PeanoNat.
Require Import Coq.Program.Basics.

(* G - носитель группы *)
Class Semigroup G : Type :=
{
    mult : G -> G -> G;
    assoc : forall x y z:G,
        mult x (mult y z) = mult (mult x y) z
}.

Class Monoid G `{Hsemi: Semigroup G} : Type :=
{
  e : G;
  left_id : forall x:G, mult e x = x;
}.

Class Group G `{Hmono: Monoid G} : Type :=
{
    inv : G -> G;
    left_inv : forall x:G, mult (inv x) x = e;
}.

Declare Scope group_scope.
Infix "*" := mult (at level 40, left associativity) : group_scope.
Open Scope group_scope.

Section Group_theorems.

  Variable G: Type.
  Context `{Hgr: Group G}.

  (* № 24 *)
  (* Вспомогательная лемма, нужна в дальнейшем *)
  (* Пусть a, b — произвольные элементы некоторой группы G. *)
  (* Доказать, что каждое из уравнений ax = b и ya = b *)
  (* имеет, и притом ровно одно, решение в данной группе. *)
  (* Условие единственности можно выразить *)
  (* следующим образом: если a*b1 = a*b2 или b1*a = b2*a, то *)
  (* b1 = b2. *)
  (* Set Printing All. *)
  Proposition left_cancel : forall x y z:G,
      x * y = x * z -> y = z.
  Proof.
    intros x y z H. assert (inv x * (x * y) = inv x * (x * z))
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

  (* Pos.to_nat *)
  (* Pos2Nat.inj_add: forall p q : positive, Pos.to_nat (p + q) = Pos.to_nat p + Pos.to_nat q *)
  (* Proposition lemma1 : forall () zpow a (Z.pos_sub p p0) = (pow a p) * inv (pow a p0). *)
    (* Search Pos_to_nat. *)
  (* Proposition a_pow_m_n : forall (a: G) (n m: nat), (pow a n)*(pow a m) = pow a (n + m). *)

  (* Proposition pow_i_neq_poq_j: *)
  (*   forall i j a n, order a n ->  i < j < n -> *)
  (*              pow a i <> pow a j. *)

  (*   forall (i, j: nat) (a: G) (n: nat), order a n ->  i < j < n -> *)
  (*              pow a i <> pow a j. *)
  (*   Proof. *)
  (*     intro. *)

Class r_action (S: Type) (r_action: S -> G -> S) : Type :=
{
  property: forall (x y: G) (s: S), r_action s (x*y) = r_action (r_action s x) y;
  e_property: forall (s: S), r_action s e = s
}.

Instance exists_GG : r_action G (mult) :=
{
  property := fun x y s => assoc s x y;
  e_property := right_id
}.

Definition commutative_group := forall (x y : G),
    (mult x y) = (mult y x).

End Group_theorems.

Section Homomorphismus.

  Variable G: Type.
  Context `{Hgr: Group G}.

  Variable F: Type.
  Context `{Fgr: Group F}.

  Record Homomorphism: Type :=
    Build_homomorphism
    {
        f: G -> F;
        proof: forall (x y: G), f (mult x y) = mult (f x) (f y)
    }.

  Theorem homo1 (phi: Homomorphism) (Hcomm: commutative_group G) (Hsur: forall (f1: F), exists (g: G), (f phi g) = f1):
      (commutative_group F).
  Proof.
    unfold commutative_group. intros. destruct (Hsur x). destruct (Hsur y). rewrite <- H. rewrite <- H0. rewrite <- (proof phi x0). rewrite <- (proof phi x1). rewrite (Hcomm x0 x1). reflexivity.
  Qed.

  (* 133. Доказать, что при гомоморфизме группы G в *)
(* группу F единица группы G переходит в единицу группы F . *)
  Theorem homo2 (phi: Homomorphism): (f phi e) = e.
  Proof.
    apply left_cancel with (Hsemi := Hsemi0) (Hmono := Hmono0) (x := (f phi e)).
    - apply Fgr.
    - rewrite  <- (proof phi e). rewrite left_id. rewrite (@right_id F _ _ Fgr). reflexivity.
  Qed.

End Homomorphismus.

Axiom functional_extensionality :
  forall A (B : A -> Type)
         (f g : forall a, B a),
    (forall a, f a = g a) ->
    f = g.

Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

(* Print exist. *)
(* Lemma l (r1 r2 : { R : nat -> nat -> bool | *)
(*                    forall n, R n n = true }) : *)
(*   (forall n1 n2, proj1_sig r1 n1 n2 = proj1_sig r2 n1 n2) -> *)
(*   r1 = r2. *)
(* Proof. *)
(*   destruct r1 as [r1 H1], r2 as [r2 H2]. *)
(*   simpl. *)
(*   intros H. *)
(*   assert (H': r1 = r2). *)
(*   { apply functional_extensionality. *)
(*     intros n1. *)
(*     apply functional_extensionality. *)
(*     intros n2. *)
(*     apply H. } *)
(*   subst r2. *)
(*   rename r1 into r. *)
(*   f_equal. *)
(*   apply proof_irrelevance. *)
(* Qed. *)

(* Inductive bool: Set := *)
(*   | true *)
(*   | false. *)

(* Lemma equality_commutes: *)
(*   forall (a: bool) (b: bool), a = b -> b = a. *)
(* Proof. *)
(*   intros. *)
(*   subst a. *)
(*   reflexivity. *)
(* Qed. *)

Inductive megaeq: forall (A B: Type) (x: A) (y: B), Prop :=
  megarefl A x : megaeq A A x x.

Search "megaeq".

Section Subgroup.
  (* Пусть дано множество - носитель группы *)
  Variable G: Type.
  (* Групповые свойства *)
  Context `{Hgr: Group G}.

  (* Предикат, определяющий подмножество *)
  Variable P : G -> Prop.
  (* Единица принадлежит подмножеству *)
  Variable s_e: P(e).
  (* Умножение 2-х элементов подмножества принадлежит подмножеству *)
  Variable mul_axiom: forall x y: sig P, P (proj1_sig x * proj1_sig y).
  (* Обратный элемент для элемента подмножества принадлежит подмножеству *)
  Variable inv_axiom: forall x: sig P, P (inv (proj1_sig x)).

  (* Ф-ция умножения 2-х элементов подмножества: *)
  (* (умножение 2-х первых проекций | s_mul) *)
  Definition mult1 x y := exist P (proj1_sig x * proj1_sig y) (mul_axiom x y).
  (* Ф-ция получения обратного элемента для данного элемента подмножества *)
  Definition inv1 (x: sig P) : sig P := exist P (inv (proj1_sig x)) (inv_axiom x).

  Theorem assoc1: forall x y z: sig P,
      mult1 x (mult1 y z) = mult1 (mult1 x y) z.
  Proof.
    intros [x Px] [y Py] [z Pz].
    set (Hproj1 := assoc x y z).
    - unfold mult1. simpl. set (R := exist P (x * (y * z))
    (mul_axiom (exist P x Px)
           (exist P (y * z) (mul_axiom (exist P y Py) (exist P z Pz))))).
      set (L := exist P (x * y * z)
                      (mul_axiom
                         (exist P (x * y) (mul_axiom (exist P x Px) (exist P y Py)))
                         (exist P z Pz))).
      set (Q := @eq_sig G P R L Hproj1). apply Q. simpl. apply proof_irrelevance.
  Qed.

  Instance semigroupSubgroup : Semigroup (sig P) :=
  {
    mult := mult1;
    assoc := assoc1
  }.

  (* e с доказательством того, что e принадлежит подмножеству *)
  Definition sub_e := exist P e s_e.
  Theorem subgroup_left_id: forall x: (sig P), mult1 sub_e x = x.
  Proof.
    intros [x Px]. set (x_pair := exist P x Px). unfold mult1. simpl. set (Q := @eq_sig G P (exist P (e * x) (mul_axiom sub_e x_pair)) x_pair). simpl in Q. apply (Q (left_id _)). apply proof_irrelevance.
  Qed.

  Instance monoidSubgroup : Monoid (sig P) :=
  {
    e := sub_e;
    left_id := subgroup_left_id;
  }.

  Definition sub_inv (x: sig P): sig P := exist P (inv (proj1_sig x)) (inv_axiom x).
  Theorem subgroup_left_inv: forall x: (sig P), mult1 (inv1 x) x = sub_e.
  Proof.
    intros [x Px]. set (x_pair := exist P x Px). unfold mult1. simpl.
    set (Q := @eq_sig G P (exist P (inv x * x) (mul_axiom (inv1 x_pair) x_pair)) sub_e). simpl in Q.
    apply (Q (left_inv x)). apply proof_irrelevance.
  Qed.

  Instance subgroup_Group : Group (sig P) :=
  {
    inv := sub_inv;
    left_inv := subgroup_left_inv;
  }.
End Subgroup.
Close Scope group_scope.
