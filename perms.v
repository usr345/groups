From mathcomp Require Import seq ssreflect ssrfun ssrbool eqtype ssrnat.

Section InductivePermutations.

Inductive l_perm {A : Type} : seq A -> seq A -> Prop :=
| permutation_nil : l_perm [::] [::]
| permutation_skip a v1 v2 of
    l_perm v1 v2 : l_perm (a :: v1) (a :: v2)
| permutation_swap a b v1 v2 of
    l_perm v1 v2 : l_perm [:: a, b & v1] [:: b, a & v2]
| permutation_trans v1 v2 v3 of
    l_perm v1 v2 & l_perm v2 v3 : l_perm v1 v3.

Theorem a_perm_b_comm (A: Type) (a b: seq A): l_perm a b -> l_perm b a.
Proof.
  elim; try by constructor.
  move=> a0 b0 v1 v2 H1 H2 IH. apply: (permutation_trans _ b0); done.
Qed.

Theorem perm_trans (A: Type) (a b c: seq A): l_perm a b -> l_perm b c -> l_perm a b.
Proof.
  elim; try by constructor.
  move=> v1 v2 *. apply: (permutation_trans _ v2); done.
Qed.

Inductive In (A: Type) (x: A) : forall (s: seq A), Type :=
| fst (t: seq A): In (x :: t)
(* | n_fst (y: A) (t: seq A) (P: In x t) : In x (y::t) *)
.

Theorem perm_x_in (A: Type) (x: A)  (a b: seq A): List.In x a -> l_perm a b -> List.In x b.
Proof.
  elim.

Record perm (n: nat) : Type := { l: list nat; p: l_perm (iota 0 n) l }.


Definition mult

perm1 := perm
End InductivePermutations.
