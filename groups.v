Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import PeanoNat.
Require Import Bool.
Require Import Coq.Program.Basics.

(* Locate "*". *)
(* Definition aaa (l: (list nat * bool)): nat := fold_left mult 0 if evenb. *)

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
  left_id : forall x: G, mult e x = x;
}.

Class Group G `{Hmono: Monoid G} : Type :=
{
    inv : G -> G;
    left_inv : forall x: G, mult (inv x) x = e;
}.

Class AbelianGroup G `{Hgr: Group G} : Type :=
{
    comm : forall (x y : G), mult x y = mult y x;
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
  Proposition left_cancel : forall a x y:G,
      a * x = a * y -> x = y.
  Proof.
    intros a x y H. assert (inv a * (a * x) = inv a * (a * y))
      as Hinvx.
    - rewrite H. reflexivity.
    - repeat rewrite assoc in Hinvx. rewrite left_inv in Hinvx. repeat rewrite left_id in Hinvx. assumption.
  Qed.

  Proposition left_cancel_alt_proof : forall a x y:G,
      a * x = a * y -> x = y.
  Proof.
    intros a x y H.
    (* Здесь самое интересное: по сути это умножение гипотезы слева на inv a *)
    (* f_equal : forall (A B : Type) (f : A -> B) (x y : A), *)
    (*    x = y -> f x = f y *)
    apply f_equal with (f := fun g:G => inv a * g) in H. repeat rewrite assoc in H. repeat rewrite left_inv in H. repeat rewrite left_id in H. assumption.
  Qed.

  Proposition right_id : forall x:G, x * e = x.
  Proof.
    intro. apply left_cancel with (a := inv x). rewrite assoc. repeat rewrite left_inv. rewrite left_id. reflexivity.
  Qed.

  Proposition right_inv:
    forall x:G, x * inv x = e.
  Proof.
    intro. apply left_cancel with (a := inv x). rewrite assoc.
    rewrite left_inv. rewrite left_id. rewrite right_id. reflexivity.
  Qed.

  Proposition right_inv_unique: forall x y:G, x * y = e -> inv x = y.
  Proof.
    intros x y H. apply left_cancel with (a := x). transitivity e.
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

Section Subgroup.
  (* Пусть дано множество - носитель группы *)
  Variable G: Type.
  (* Групповые свойства *)
  Context `{Hgr: Group G}.

  Axiom functional_extensionality :
  forall A (B : A -> Type)
         (f g : forall a, B a),
    (forall a, f a = g a) ->
    f = g.

  Axiom proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.

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

  Context `{Hab: @AbelianGroup G _ _ Hgr}.

  Theorem AbelianSubgroup_Abelian: forall x y: (sig P), x * y = y * x.
  Proof.
    intros. set (Q := @eq_sig G P (x*y) (y*x)). simpl in Q. apply (Q (comm (proj1_sig x) (proj1_sig y))). apply proof_irrelevance.
  Qed.

  Instance Abelian_subgroup_Group : AbelianGroup (sig P) :=
  {
    comm := AbelianSubgroup_Abelian;
  }.

  Definition Normal_subgroup (x y: G) (p: P x) := P (conjugation G x y).

  (* Сопряжение - это изоморфизм группы в саму себя *)
  (* 99 Докажите, что в коммутативной группе всякая подгруппа является нормальной подгруппой. *)

  Theorem EveryAbelianSubgroup_normal: forall (x: sig P) (y: G), Normal_subgroup (proj1_sig x) y (proj2_sig x).
  Proof.
    intros x y. destruct x. simpl. unfold Normal_subgroup. unfold conjugation. rewrite comm. rewrite assoc. rewrite right_inv. rewrite left_id. apply p.
  Qed.

End Subgroup.

Section Homomorphismus.

  Variable G: Type.
  Context `{Gsemi: Semigroup G}.

  Variable F: Type.
  Context `{Fsemi: Semigroup F}.

  Record Homomorphism: Type :=
    Build_homomorphism
    {
        f: G -> F;
        proof: forall (x y: G), f (mult x y) = mult (f x) (f y)
    }.

    Record Isomorphism: Type :=
    Build_isomorphism
      {
        fun1: Homomorphism;
        fun2: F -> G;
        left_right_id: forall (x: G), fun2 ((f fun1) x) = x;
        right_left_id: forall (y: F), (f fun1) (fun2 y) = y;
        (* Homo_f: forall (a b: G), fun1 (a * b) = (fun1 a) * (fun1 b); *)
        (* Homo_right: forall (a b: G2), right (a * b) = (right a) * (right b) *)
      }.

  Theorem homo1 (phi: Homomorphism) (Hcomm: commutative_group G) (Hsur: forall (f1: F), exists (g: G), (f phi g) = f1):
      (commutative_group F).
  Proof.
    unfold commutative_group. intros. destruct (Hsur x). destruct (Hsur y). rewrite <- H. rewrite <- H0. rewrite <- (proof phi x0). rewrite <- (proof phi x1). rewrite (Hcomm x0 x1). reflexivity.
  Qed.

  (* 133. Доказать, что при гомоморфизме группы G в *)
  (* группу F единица группы G переходит в единицу группы F . *)
  Theorem homomorphism_saves_e: forall (phi: Homomorphism) `{Hmono: @Monoid G Gsemi} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono}, (f phi) e = e.
  Proof.
    intros. apply (left_cancel_alt_proof F (f phi e)). rewrite <- (proof phi e e). rewrite left_id. rewrite right_id.
    - reflexivity.
    - apply Fgroup.
  Qed.
    (* Theorem homo2 (phi: Homomorphism): (f phi e) = e. *)
  (* Proof. *)
  (*   apply left_cancel with (Hsemi := Hsemi0) (Hmono := Hmono0) (x := (f phi e)). *)
  (*   - apply Fsemi. *)
  (*   - rewrite  <- (proof phi e). rewrite left_id. rewrite (@right_id F _ _ Fsemi). reflexivity. *)
  (* Qed. *)

  (* 134 *)
  Theorem homomorphism_saves_inv: forall (x: G) (phi: Homomorphism) `{Hmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Hmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono}, (f phi (inv x)) = inv (f phi x).
  Proof.
    intros. apply (left_cancel_alt_proof F (f phi x)). rewrite <- (proof phi). rewrite right_inv. rewrite right_inv. apply homomorphism_saves_e. apply Fgroup.
  Qed.

  Definition Im_prop (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (y: F) := exists x: G, y = (f phi x).

  Definition Im (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} := sig (Im_prop phi).

  Definition Im_mult (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x y: (Im phi)): Im phi.
  Proof.
    exists (mult (proj1_sig x) (proj1_sig y)). unfold Im_prop. destruct x. destruct y. destruct i. destruct i0. simpl. exists (x1*x2). rewrite (proof phi). rewrite <- e0. rewrite <- e1. reflexivity.
  Defined.

  Theorem Im_mult_assoc: forall (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x y z: Im phi), Im_mult phi x (Im_mult phi y z) = Im_mult phi (Im_mult phi x y) z.
  Proof.
    intros phi Gmono Ggroup Fmono Fgroup x y z. unfold Im_mult. destruct x. destruct y. destruct z. simpl. destruct i. destruct i0. destruct i1. assert (Hproj1: x * (x0 * x1) = (x * x0 * x1)).
    - apply assoc.
    - match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end.
      set (Q := @eq_sig F (Im_prop phi) name1 name2 Hproj1). apply Q. simpl. apply proof_irrelevance.
  Qed.

  Instance semigroupIm (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Semigroup (@Im phi Gmono Ggroup Fmono Fgroup) :=
  {
    mult := Im_mult phi;
    assoc := Im_mult_assoc phi
  }.

  Definition Im_e (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Im phi.
  Proof.
    exists e. exists e. symmetry. apply homomorphism_saves_e. apply Fgroup.
  Defined.

  Theorem Im_mult_left_id: forall (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x: (Im phi)), Im_mult phi (Im_e phi) x = x.
  Proof.
    intros phi Gmono Ggroup Fmono Fgroup x. unfold Im_mult. destruct x as [x0 Px]. destruct Px. assert (H_left_id: e * x0 = x0).
    - apply left_id.
    - simpl. match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig F (Im_prop phi) name1 name2 H_left_id). apply Q. simpl. apply proof_irrelevance.
  Qed.

  Instance monoidIm (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Monoid (@Im phi Gmono Ggroup Fmono Fgroup) :=
  {
    e := Im_e phi;
    left_id := Im_mult_left_id phi
  }.

  Definition Im_inv (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x: (Im phi)) : Im phi.
  Proof.
    destruct x as [y P]. exists (inv y). destruct P as [x H]. set(H_inv := homomorphism_saves_inv x). exists (inv x). rewrite H. symmetry. apply H_inv.
  Defined.

  Theorem Im_mult_left_inv: forall (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x: (Im phi)), Im_mult phi (Im_inv phi x) x = Im_e phi.
  Proof.
    intros phi Gmon Ggroup Fmono Fgroup x. unfold Im_mult. destruct x as [y P]. destruct P as [x Py]. simpl. assert (H_left_inv: inv y * y = e).
    - apply left_inv.
    - match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig F (Im_prop phi) name1 name2 H_left_inv). apply Q. apply proof_irrelevance.
  Qed.

  Instance groupIm (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Group (@Im phi Gmono Ggroup Fmono Fgroup) :=
  {
    inv := Im_inv phi;
    left_inv := Im_mult_left_inv phi
  }.

  (* Ядро гомоморфизма *)
  Definition Ker (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} := sig (fun x => (f phi x) = e).

  Definition Ker_mult (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x y: Ker phi): Ker phi.
  Proof.
    destruct x as [x Px]. destruct y as [y Py]. exists (mult x y). rewrite (proof phi). rewrite Px. rewrite Py. rewrite left_id. reflexivity.
  Defined.

  Theorem Ker_mult_assoc: forall (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x y z: Ker phi), Ker_mult phi x (Ker_mult phi y z) = Ker_mult phi (Ker_mult phi x y) z.
  Proof.
    intros phi Gmono Ggroup Fmono Fgroup x y z. destruct x as [x Px]. destruct y as [y Py]. destruct z as [z Pz]. unfold Ker_mult.
    assert (Hassoc: x * (y * z) = (x * y * z)).
    - apply assoc.
    - match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig G (fun x => (f phi x) = e) name1 name2 Hassoc). apply Q. unfold proj1_sig. unfold proj2_sig. simpl. apply proof_irrelevance.
  Qed.

  Instance semigroupKer (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Semigroup (@Ker phi Gmono Ggroup Fmono Fgroup) :=
  {
    mult := Ker_mult phi;
    assoc := Ker_mult_assoc phi
  }.

  Definition Ker_e (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Ker phi.
  Proof.
    exists e. apply homomorphism_saves_e. apply Fgroup.
  Defined.

  Theorem Ker_mult_left_id: forall (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x: (Ker phi)), Ker_mult phi (Ker_e phi) x = x.
  Proof.
    intros phi Gmono Ggroup Fmono Fgroup x. destruct x as [x0 Px]. unfold Ker_mult. unfold Ker_e. assert (Hleft_id: e * x0 = x0).
    - apply left_id.
    - match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig G (fun x => (f phi x) = e) name1 name2 Hleft_id). apply Q. simpl. apply proof_irrelevance.
  Qed.

  Instance monoidKer (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Monoid (@Ker phi Gmono Ggroup Fmono Fgroup) :=
  {
    e := Ker_e phi;
    left_id := Ker_mult_left_id phi
  }.

  Definition Ker_inv (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x: (Ker phi)): Ker phi.
  Proof.
    destruct x as [x P]. exists (inv x). rewrite (@homomorphism_saves_inv x phi Gmono Ggroup Fmono Fgroup). rewrite P. apply e_inv.
  Defined.

  Theorem Ker_mult_left_inv: forall (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} (x: (Ker phi)), Ker_mult phi (Ker_inv phi x) x = Ker_e phi.
  Proof.
    intros phi Gmono Ggroup Fmono Fgroup x. destruct x as [x0 Px]. unfold Ker_mult. unfold Ker_e. unfold Ker_inv. assert (Hinv: (inv x0) * x0 = e).
    - apply left_inv.
    - match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig G (fun x => (f phi x) = e) name1 name2 Hinv). apply Q. apply proof_irrelevance.
  Qed.

  Instance groupKer (phi: Homomorphism) `{Gmono: @Monoid G Gsemi} `{Ggroup: @Group G Gsemi Gmono} `{Fmono: @Monoid F Fsemi} `{Fgroup: @Group F Fsemi Fmono} : Group (@Ker phi Gmono Ggroup Fmono Fgroup) :=
  {
    inv := Ker_inv phi;
    left_inv := Ker_mult_left_inv phi
  }.

End Homomorphismus.

(* 135. Пусть f1 : G → F и f2 : F → H — гомоморфизмы. *)
(* Доказать, что f2 f1 : G → H — гомоморфизм. *)
Theorem homomorphism_mult_homo: forall (G F H: Type) `{Gsemi: Semigroup G} `{Fsemi: Semigroup F} `{Hsemi: Semigroup H} (phi1: Homomorphism G F) (phi2: Homomorphism F H) (x y: G), (f F H phi2 (f G F phi1 (x*y))) = (f _ _ phi2 (f _ _ phi1 x)) * (f _ _ phi2 (f _ _ phi1 y)).
Proof.
  intros. rewrite (proof G F). rewrite (proof F H). reflexivity.
Qed.

Definition homomorphism_composition (G F H: Type) `{Gsemi: Semigroup G} `{Fsemi: Semigroup F} `{Hsemi: Semigroup H} (phi1: Homomorphism G F) (phi2: Homomorphism F H) := Build_homomorphism G H (fun x: G => (f F H phi2) (f G F phi1 x)) (homomorphism_mult_homo G F H phi1 phi2).
(* Section Isomorphismus. *)

  (* Record Isomorphism: Type := *)
  (*   Build_isomorphism *)
  (*   { *)
  (*       phi: G1 -> G2; *)
  (*       totality: forall (x: G1), exists (y: G2), phi x = y; *)
  (*       injectivity: forall (x1 x2: G1), (phi x1) = (phi x2) -> x1 = x2; *)
  (*       operation_preservation: forall (a b: G1), phi (a * b) = (phi a) * (phi b) *)
  (*   }. *)

(* End Isomorphismus. *)

Theorem th01: forall (G F: Type) `{Hgr1: Semigroup G} `{Hgr2: Semigroup F} (phi: Isomorphism G F), forall (a b: F), (fun2 _ _ phi) (a * b) = ((fun2 _ _ phi) a) * ((fun2 _ _ phi) b).
Proof.
  intros. rewrite <- (right_left_id _ _ phi a). rewrite <- (right_left_id _ _ phi b). rewrite <- (proof G F (fun1 _ _ phi)). repeat rewrite (left_right_id _ _ phi). reflexivity.
Qed.

Theorem th1: forall (G F: Type) `{Hgr1: Semigroup G} `{Hgr2: Semigroup F} (phi: Isomorphism G F), Isomorphism F G.
Proof.
  intros. set (Homo2 := th01 G F phi). set (phi1 := phi). destruct phi. simpl in Homo2.
  set (Homo1 := Build_homomorphism F G fun4 Homo2).
  apply (Build_isomorphism F G Homo1 (f G F fun3)).
  - apply (right_left_id G F phi1).
  - apply (left_right_id G F phi1).
Qed.

(* Если группа изоморфна полугруппе, то полугруппа является группой *)
   (* compose (phi1.(phi)) (psi.(phi)) =1 id). *)

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

Section generatedSubgroup.
  (* Пусть дано множество - носитель группы *)
  Variable G: Type.
  (* Групповые свойства *)
  Context `{Hgr: Group G}.

  Definition id_or_inv (P1: G -> Prop): Type := ((sig P1) * bool).
  Definition invert_list (P: G -> Prop) (l: list (id_or_inv P)): (list (id_or_inv P)) :=
    rev (
        map
          (fun x => (fst x, negb (snd x)))
          l).

  Lemma inv_app (P: G -> Prop) (l1: list (id_or_inv P)) (l2: list (id_or_inv P)):
      invert_list P (l1 ++ l2) = invert_list P l2 ++ invert_list P l1.
  Proof.
    destruct l1 as [| x t].
    - unfold invert_list. simpl. rewrite app_nil_r. reflexivity.
    - unfold invert_list. simpl. rewrite map_app. rewrite rev_app_distr. rewrite <- app_assoc. reflexivity.
  Qed.

  Definition gfold (P1: G -> Prop) (l: list (id_or_inv P1)) :=
    fold_right
      mult e
      (map (fun (v: (sig P1) * bool) =>
              if snd v
              then (proj1_sig (fst v))
              else inv (proj1_sig (fst v)))
           l).

  (* Порождающее множество группы G — это подмножество S в G, такое, что каждый элемент G может быть записан как произведение конечного числа элементов S и их обратных.  *)
  Definition generatedSubgroup (P1: G -> Prop) :=
    sig (fun x =>
           @ex
             (list (id_or_inv P1))
             (fun l =>
                (x = gfold P1 l))).


  Theorem generatedSubgroup_mul: forall (P1: G -> Prop) (x y: list (id_or_inv P1)), gfold P1 (x ++ y) = gfold P1 x * gfold P1 y.
  Proof.
    intros. unfold gfold. induction x as [|x0 x].
    - simpl. rewrite left_id. reflexivity.
    - simpl. rewrite <- assoc. rewrite IHx. reflexivity.
  Qed.

  Lemma unapp L (x: L) (l: list L): x::l = (x::nil)++l.
  Proof.
    reflexivity.
  Qed.

  Lemma gfold_inv (P: G -> Prop) (l: list (id_or_inv P)): gfold P (invert_list P l) = inv (gfold P l).
  Proof.
    induction l as [|x t].
    - unfold gfold. simpl. symmetry. apply e_inv.
    - rewrite unapp. rewrite inv_app. rewrite generatedSubgroup_mul. rewrite generatedSubgroup_mul. rewrite inv_prod. rewrite IHt. unfold gfold. simpl. destruct (snd x).
      +  simpl. repeat rewrite right_id. reflexivity. apply Hgr. apply Hgr.
      + simpl. repeat rewrite right_id. rewrite inv_involution. reflexivity. apply Hgr. apply Hgr.
  Qed.


  Definition mult_gen (P1: G -> Prop) (x y: generatedSubgroup P1): generatedSubgroup P1.
  Proof.
    unfold generatedSubgroup. destruct x as [x0 Px]. destruct y as [y0 Py]. exists (x0 * y0). destruct Px as [list_x Px]. destruct Py as [list_y Py]. exists (list_x ++ list_y). symmetry. rewrite Px. rewrite Py. apply generatedSubgroup_mul.
  Defined.

  Theorem generatedSubgroup_assoc: forall (P1: G -> Prop) (x y z: generatedSubgroup P1), mult_gen P1 x (mult_gen P1 y z) = mult_gen P1 (mult_gen P1 x y) z.
  Proof.
    intros. assert (Hproj1: proj1_sig (mult_gen P1 x (mult_gen P1 y z)) = proj1_sig (mult_gen P1 (mult_gen P1 x y) z)).
    - destruct x as [x Px]. destruct y as [y Py]. destruct z as [z Pz]. unfold mult_gen. simpl.
      rewrite assoc. reflexivity.
    - destruct x as [x Px]. destruct y as [y Py]. destruct z as [z Pz]. unfold mult_gen. simpl.
      match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig G _ name1 name2 Hproj1). apply Q. simpl. apply proof_irrelevance. (* unfold eq_rect. destruct Px as [x0 Px]. destruct Py as [y0 Py]. destruct Pz as [z0 Pz]. subst. simpl. unfold eq_sym. unfold eq_ind_r. unfold eq_ind. simpl. assert (Hassoc: x0 ++ y0 ++ z0 = (x0 ++ y0) ++ z0). *)
      (* + apply app_assoc. *)
      (* + match goal with |- ?L = ?R => set (name3 := L); set (name4 := R) end. set (Q := @eq_sig (list (id_or_inv P1)) _ name3 name4 Hassoc). *)
  Qed.

  Instance semigroupGeneratedSubgroup (P1: G -> Prop) : Semigroup (generatedSubgroup P1) :=
  {
    mult := mult_gen P1;
    assoc := generatedSubgroup_assoc P1
  }.

  Definition e_gen (P1: G -> Prop): generatedSubgroup P1.
  Proof.
    unfold generatedSubgroup. exists e. exists nil. unfold gfold. simpl. reflexivity.
  Defined.

  Theorem generatedSubgroup_left_id: forall (P1: G -> Prop) (x: generatedSubgroup P1), mult_gen P1 (e_gen P1) x = x.
  Proof.
    intros. destruct x as [x Px]. unfold e_gen. simpl. unfold mult_gen. simpl. match goal with |- ?L = ?R => set (name1 := L); set (name2 := R) end. set (Q := @eq_sig G _ name1 name2 (left_id x)). apply Q. simpl. apply proof_irrelevance.
Qed.

  Instance monoidGeneratedSubgroup (P1: G -> Prop) : Monoid (generatedSubgroup P1) :=
  {
    e := e_gen P1;
    left_id := generatedSubgroup_left_id P1
  }.

  Definition inv_gen (P1: G -> Prop) (x: generatedSubgroup P1): generatedSubgroup P1.
  Proof.
    unfold generatedSubgroup. destruct x as [x Px]. exists (inv x). unfold gfold. destruct Px as [l0 Px]. simpl. reflexivity.
  Defined.


  (* Definition commutant := { x : G | exists l: list (G*G), x = fold (fun p a => mult1 (commutator (fst p) (snd p)) a) e l }. *)
End generatedSubgroup.


Section CartesianGroupProduct.
  (* Пусть дано множество - носитель группы *)
  Variable G: Type.
  Variable H: Type.
  (* Групповые свойства *)
  Context `{Hgr1: Group G}.
  Context `{Hgr2: Group H}.

  Definition mulp (x y : G * H): (G * H) := (mult (fst x) (fst y), mult (snd x) (snd y)).

  Theorem assocGroupProduct: forall x y z: G * H,
      mulp x (mulp y z) = mulp (mulp x y) z.
  Proof.
    intros. unfold mulp. simpl. rewrite (@assoc G). rewrite (@assoc H). reflexivity.
  Qed.

  Instance semigroupGroupProduct : Semigroup (G * H) :=
  {
    mult := mulp;
    assoc := assocGroupProduct;
  }.

  Definition groupProduct_e: (G * H) := (e, e).

  Theorem GroupProductLeftId: forall x: G * H,
      mult groupProduct_e x = x.
  Proof.
    intros. unfold groupProduct_e. destruct x. unfold mult. simpl. unfold mulp. simpl. repeat rewrite left_id. reflexivity.
  Qed.

  Instance monoidGroupProduct : Monoid (G * H) :=
  {
    e := groupProduct_e;
    left_id := GroupProductLeftId;
  }.

  Definition groupProduct_inv (x: G*H) := (inv (fst x), inv(snd x)).

  Theorem groupProduct_left_inv : forall x: (G * H), mult (groupProduct_inv x) x = groupProduct_e.
  Proof.
    intros. destruct x. unfold mult. simpl. unfold mulp. simpl. repeat rewrite left_inv. unfold groupProduct_e. reflexivity.
  Qed.

  Instance groupGroupProduct : Group (G * H) :=
  {
      inv := groupProduct_inv;
      left_inv := groupProduct_left_inv;
  }.

  Theorem projectHomomorphismus : forall (x y: (G * H)), fst (mult x y) = mult (fst x) (fst y).
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Theorem projectHomomorphismus2 : forall (x y: (G * H)), snd (mult x y) = mult (snd x) (snd y).
  Proof.
    intros. simpl. reflexivity.
  Qed.

  Definition rec_fst := Build_homomorphism (G*H) G fst projectHomomorphismus.

  Definition rec_snd := Build_homomorphism (G*H) H snd projectHomomorphismus2.

  Definition get_e_pair (x: G): (G*H) := (x, e).

  Theorem projectHomomorphismus3 : forall (x y: G), get_e_pair (mult x y) = mult (get_e_pair x) (get_e_pair y).
  Proof.
    intros. unfold get_e_pair. simpl. unfold mulp. simpl. rewrite left_id. reflexivity.
  Qed.

  Definition rec_get_e_pair := Build_homomorphism G (G*H) get_e_pair projectHomomorphismus3.

  Context `{Gab: @AbelianGroup G Hsemi Hmono Hgr1}.
  Context `{Hab: @AbelianGroup H _ _ Hgr2}.

  Theorem AbelianProduct: forall (x y : (G*H)), mult x y = mult y x.
  Proof.
    intros. unfold mult. simpl. unfold mulp. rewrite (@comm G _ _ _ Gab). rewrite (@comm H _ _ _ Hab). reflexivity.
  Qed.
End CartesianGroupProduct.
Close Scope group_scope.
