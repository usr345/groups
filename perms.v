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

Inductive In {A: Type} (x: A) : seq A -> Prop :=
| fst (t: seq A): In x (x :: t)
| n_fst (y: A) (t: seq A) (H: In x t) : In x (y::t)
.

Theorem perm_x_in (A: Type) (x: A)  (a b: seq A): In x a -> l_perm a b -> In x b.
Proof.
  move=> H1 H2. move: H1. elim: H2.
  - apply.
  - move=> a0 v1 v2 H1 H2 H3. inversion H3. subst.
    + apply (fst a0 v2).
    + subst. apply n_fst. apply H2 in H0. apply H0.
  - move=> a0 v1 v2 H1 H2 H3 H4. inversion H4.
    + apply n_fst. apply fst.
    + subst. inversion_clear H0.
      * apply fst.
      * apply n_fst. apply n_fst. apply (H3 H).
  - move=> a0 v1 v2 H1 H2 H3 H4 H5. apply H4. apply H2. exact H5.
Qed.

Record perm (n: nat) : Type := { l: list nat; p: l_perm (iota 0 n) l }.


Definition mult

perm1 := perm
End InductivePermutations.
