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
  (* Lt.lt_S_n: *)
  (* forall n m : nat, Datatypes.S n < Datatypes.S m -> n < m *)



    + destruct x.
      * destruct y.
        ** intros H. discriminate H.
        ** destruct y. reflexivity. intros H. discriminate H.
      * destruct x.
        ** destruct y. intros H. discriminate H. destruct y. intros H. discriminate H.




Lemma imya: self_isometry Z_3 triangle rotate.
Proof.
  unfold self_isometry. intros. destruct s1. destruct s2.

  destruct (Nat.eqb n0 n1) eqn:E.
  - apply PeanoNat.Nat.eqb_eq in E. simpl. rewrite E. rewrite (PeanoNat.Nat.eqb_refl n1). apply PeanoNat.Nat.eqb_refl.
  - simpl. destruct n0; destruct n1.
    + simpl. apply PeanoNat.Nat.eqb_refl.
    + destruct n1. simpl. destruct x.
      * simpl.


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
