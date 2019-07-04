(* PROGRAMMING WITH DEPENDENT TYPES *)

(* To get mark 3, solve exercises 1-3.
   To get mark 4, solve exercises 1-4.
   To get mark 5, solve exercises 1-5. *)

Require Import Arith Bool List Eqdep Utf8 Omega.

(*Require Import CpdtTactics.*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil  : ilist 0
  | Cons : forall n, A -> ilist n -> ilist (S n)
  .

  (* Exercise 1 *)

  (* Define a strongly specified function which returns the tail of
     a length-indexed list. *)

  Definition tail (n : nat) (l : ilist (S n)) :
    {l' : ilist n | ∃ x, Cons x l' = l}.
  Proof.
    refine (
    match l with
        | Cons _ h t => exist _ t _
    end).
    exists h. reflexivity. Show Proof.
  Defined.

End ilist.

(* Exercise 2 *)

(* Define an inductive dependently-typed datatype representing strongly
   specified AVL trees in such a way that every valid value of this
   datatype represents a balanced tree (2 * minimum depth ≥ maximum depth).
   The depth of the tree should be a part of its type. The tree should
   store natural numbers in its nodes. *)

Inductive AvlTree : nat -> Set :=
    | E : AvlTree 0
    | T : forall n m : nat, n <= S m -> m <= S n ->
        nat -> AvlTree n -> AvlTree m -> AvlTree (S (max n m)).

(* Exercise 3 *)

(* Prove that all AVL trees are balanced. *)

Require Import Max Min.
Section depth.
  Variable f : nat → nat → nat.

  Fixpoint depth (n : nat) (t : AvlTree n) : nat :=
  match t with
      | E => 0
      | T _ _ _ _ _ l r => S (f (depth l) (depth r))
  end.
End depth.

Ltac minmax := repeat
match goal with
    | H : ?x = _ |- context [?x] => rewrite H
    | |- context [max ?a ?b] => decompose [and or] (max_spec a b)
    | |- context [min ?a ?b] => decompose [and or] (min_spec a b)
end. 

Lemma depth_min_max :
  forall (n : nat) (t : AvlTree n), depth min t <= depth max t.
Proof.
  induction t as [| n m Hnm Hmn v l IHl r IHr]; cbn.
    trivial.
    apply le_n_S. minmax; firstorder omega.
Qed.

Theorem balanced : ∀ n (t : AvlTree n), 2 * depth min t ≥ depth max t.
Proof.
  unfold ge.
  induction t as [| n m Hnm Hmn v l IHl r IHr]; cbn.
    trivial.
    apply le_n_S. minmax; try omega; cbn in *; rewrite plus_0_r in *.
Admitted.

(* Exercise 4 *)

(* Define insert function which inserts a number into the tree. Then define
   predicate present which checks if an element is stored in the tree.
   Use present to prove that the tree after insertion contains the
   inserted element and all elements it contained before insertion. *)

(* Use datatype sum for return type of insert function (the tree after
   insertion can change its depth) *)

Check sum.
Print sum.

Section insert.
  Variable x : nat.

  Fixpoint insert n (t : AvlTree n) : AvlTree n + AvlTree (S n).
  (* FILL IN HERE *)
  Admitted.
End insert.

Section present.
  Variable z : nat.

  Fixpoint present n (t : AvlTree n) : Prop.
  (* FILL IN HERE *)
  Admitted.

  Definition present_sum n1 n2 (trees : AvlTree n1 + AvlTree n2) : Prop :=
  match trees with
  | inl t1 => present t1
  | inr t2 => present t2
  end.

  Theorem present_insert :
    ∀ n (t : AvlTree n) x, present_sum (insert x t) ↔ present t ∨ z = x.
    (* FILL IN HERE *)
  Admitted.
End present.

(* Exercise 5 *)

(* Define a predicate which checks if elements in the tree are in correct
   order (for each node, all elements in the left subtree should be smaller
   or equal and all elements in the right subtree greater or equal to the
   element stored in that node) and use it to prove that insert function
   keeps that order. *)

Fixpoint ordered n (t : AvlTree n) : Prop.
  (* FILL IN HERE *)
Admitted.

Definition ordered_sum n1 n2 (trees : AvlTree n1 + AvlTree n2) : Prop :=
  match trees with
  | inl t | inr t => ordered t
  end.

Theorem insert_ordered : ∀ n (t : AvlTree n) x, ordered t → ordered_sum (insert x t).
  (* FILL IN HERE *)
Admitted.