Add LoadPath ".".
Require Import groups.
Require Import groups_Z_n.
Import GroupZ_3.

Open Scope group_scope.
Section polygons.

  Variable G: Type.
  Context `{Hgr: Group G}.

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

  Class r_action (S : Type) (r_action: S -> G -> S) : Type :=
  {
    property: forall (x y: G) (s: S), r_action s (x*y) = r_action (r_action s x) y;
  }.

  Instance exists_GG : r_action G (mult) :=
  {
    property := fun x y s => assoc s x y
  }.

  Definition self_isometry (g: coloured_graph) (s := S g) (cg := colouring g)
             (r_a: s -> G -> s) `{HRact: r_action s r_a} := forall (s1 s2: s) (x: G), cg (r_a s1 x) (r_a s2 x) = cg s1 s2.
End polygons.

Definition triangle := Build_coloured_graph Z_3 bool Nat.eqb.
Definition rotate (z n: Z_3): Z_3 := Z3_op z n.

  (* Compute (self_isometry triangle rotate). *)
  Search "comp".

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
