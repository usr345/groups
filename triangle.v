Add LoadPath ".".
Require Import groups.
Require Import Omega.
Require Import groups_Z_n.
Import GroupZ_3.

Open Scope group_scope.

(* Раскрашенный граф - это
 * мн-во вершин (S)
 * мн-во цветов (colour)
 * ф-ция из пары вершин в цвет (colouring)
 *)
Record coloured_graph: Type :=
  Build_coloured_graph
  {
      S: Type;
      colour: Type;
      colouring: S -> S -> colour;
  }.

  (* Compute exists_GG. *)
  (* Definition r_actionZ3 := exists_GG Z_3. *)

Instance r_actionZ3: r_action Z_3 Z_3 (mult) := exists_GG Z_3.
  (* { *)
  (*   property := fun x y s => assoc s x y *)
  (* }. *)

Definition self_isometry (G: Type) `{HGroup: Group G} (g: coloured_graph) (s := S g) (cg := colouring g)
             (r_a: s -> G -> s) `{HRact: r_action G s r_a} := forall (s1 s2: s) (x: G), cg (r_a s1 x) (r_a s2 x) = cg s1 s2.

Definition triangle := Build_coloured_graph Z_3 bool Nat.eqb.
Definition rotate (z n: Z_3): Z_3 := Z3_op z n.

Search (_ < _).

Compute (self_isometry Z_3 triangle rotate).
(* Print Instances r_action. *)
(* Set Printing All. *)
Lemma a1 (x y: nat) (prf1: x < 3) (prf2: y < 3):
    match x with
    | 0 => 2
    | 1 => 1
    | Datatypes.S (Datatypes.S _) => 0
    end
    =
    match y with
    | 0 => 2
    | 1 => 1
    | Datatypes.S (Datatypes.S _) => 0
    end
    <-> x = y.
Proof.
  split.
  - destruct x as [|x1].
    + destruct y.
      *  reflexivity.
      * destruct y.
        ** intros H; discriminate H.
        ** destruct y; intros H; discriminate H.
    + destruct x1 as [|x2].
      * destruct y as [|y1].
        ** easy.
        ** destruct y1 as [|y2].
           *** reflexivity.
           *** easy.
      * destruct x2 as [|x3].
        ** destruct y as [|y1].
           *** easy.
           *** destruct y1.
               **** easy.
               **** destruct y1. reflexivity. omega.
        ** omega.
  - intros H. rewrite H. reflexivity.
Qed.

Compute Nat.divmod 4 2 0 2.
(* Lemma a2 (x y: nat) (prf1: x < 3) (prf2: y < 3): *)
(*   snd (Nat.divmod x 2 0 2) = snd (Nat.divmod y 2 0 2) <-> x = y. *)
(* Proof. *)
(*   split. *)
(*   - destruct x as [|[|[|x1]]]; simpl. *)
(*     + destruct y as [|y1]; simpl. *)
(*       * reflexivity. *)
(*       * destruct y1 as [|y2]. *)
(*         ** simpl. intro. discriminate H. *)
(*         **  *)

Search (?a =? ?b <-> ?a = ?b).
Lemma eq_bool_eq: forall (x1 x2 x3 x4: nat), ((x1 =? x2) = (x3 =? x4)) <-> (x1 = x2 <-> x3 = x4).
Proof.
  intros. split.
  - intros H. destruct (Nat.eqb_spec x1 x2); destruct (Nat.eqb_spec x3 x4). rename e into E1. rename e0 into E2.
    + rewrite E1. rewrite E2. split; reflexivity.
    + discriminate H.
    + discriminate H.
    + split.
      * intros. rewrite H0 in n0. exfalso. apply n0. reflexivity.
      * intros. rewrite H0 in n1. exfalso. apply n1. reflexivity.
  - intros. destruct H. destruct (Nat.eqb_spec x1 x2); destruct (Nat.eqb_spec x3 x4); try reflexivity.
    + set (f := n0 (H e)). destruct f.
    + set (f := n0 (H0 e)). destruct f.
Qed.

(* Set Printing All. *)
Lemma Z3_eq1: forall (x : Z_3), Z3 (n x) (proof x) = x.
Proof.
  intros. destruct x. simpl. reflexivity.
Qed.

Set Printing All.
Lemma imya: self_isometry Z_3 triangle rotate.
Proof.
  unfold self_isometry. intros. unfold colouring. unfold rotate. unfold triangle. simpl (colour
       (Build_coloured_graph Z_3 bool
                             (fun n0 m : Z_3 => Nat.eqb (n n0) (n m)))). set (p := (proof (Z3_op s1 x))). set (q := (proof (Z3_op s2 x))). rewrite eq_bool_eq. split.
  - intros. set (E := Z3_eq (n (Z3_op s1 x)) (n (Z3_op s2 x)) p q H). repeat rewrite Z3_eq1 in E. simpl in s1, s2. set (H1 := @right_cancel Z_3 semigroupZ3 _ _ s1 s2 x E). rewrite H1. reflexivity.
  - intros. set (H1 := Z3_eq (n s1) (n s2) (proof s1) (proof s2) H). repeat rewrite Z3_eq1 in H1. rewrite H1. reflexivity.
Qed.

Definition f (x: nat) := x + 1.
Definition g (x: nat) := x + 2.

Locate "∘".
Compute (Basics.compose f g) 3.
Require Import Program.Basics.
Open Scope program_scope.
Theorem compose_assoc (A B C D: Type) (f: A -> B) (g: B -> C) (h: C -> D):
  h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof.
  unfold compose.
  reflexivity.
Qed.
Close Scope program_scope.
Close Scope group_scope.
