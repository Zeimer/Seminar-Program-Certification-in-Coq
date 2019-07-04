Require Import Utf8.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

(** **** Exercise: 1 star (beq_nat_STRONG)  *)

(** Define directly recursive function of type ∀ (n m:nat), {n = m} + {n ≠ m}.
    You can define it using tactics but remember to end definition with
    Defined.
    There's no need for using the induction tactic then. *)
Fixpoint beq_nat_STRONG (n m:nat) : {n = m} + {n ≠ m}.
Proof.
  destruct n as [| n'], m as [| m'].
    left. trivial.
    right. inversion 1.
    right. inversion 1.
    destruct (beq_nat_STRONG n' m'); [left | right]; congruence.
Defined.

(** This is a strongly specified function but we can define them also with
    their weakly specified analogues. *)

(** **** Exercise: 1 star (beq_nat_strengthened)  *)

(** Define function of the same type without using recursion. Instead of it
    you can use definitions beq_nat, beq_nat_true_iff and beq_nat_false_iff. *)
Definition beq_nat_strengthened (n m:nat) : {n = m} + {n ≠ m}.
Proof.
  case_eq (beq_nat n m); intro.
    rewrite beq_nat_true_iff in H. subst. left. reflexivity.
    rewrite beq_nat_false_iff in H. right. assumption.
Defined.

(** Sometimes first we want to build a structure of our script and after that
    fill it with remaining proofs. This can be a bit harder with strongly
    specified functions. *)

(** **** Exercise: 1 star (beq_nat_WRONG)  *)

(** Use a trick (admit or Admitted) to define function of the same times which
    lies. After that a commented out proof beq_nat_WRONG_is_wrong below should
    pass without problems. *)

Axiom wut : forall n m : nat, n = m.

Definition beq_nat_WRONG (n m : nat) : {n = m} + {n ≠ m}.
Proof.
  left. apply wut.
Defined.

Definition sumbool_to_bool {A B:Prop} (s: {A}+{B}) : bool :=
  match s with
  | left  _ => true
  | right _ => false
  end.


(*
Extract Inductive sumbool => "bool" ["True" "False"].
Extraction sumbool_to_bool.
*)

Example beq_nat_WRONG_is_wrong :
  ∀ (n m:nat), sumbool_to_bool (beq_nat_WRONG n m) = true.
Proof.
  intros n m.
  unfold sumbool_to_bool, beq_nat_WRONG.
  reflexivity.
Qed.

(** Now we'll try to see what the differences between working with weakly and
    strongly specified functions are. Below there are defined two versions of
    substitution in λ-calculus. Excersices are about proving their simple
    property to sense that differences. *)

Section Λ_exp.

Definition V := nat.

Inductive Λ : Type :=
| Λ_var : V → Λ
| Λ_abs : V → Λ → Λ
| Λ_app : Λ → Λ → Λ.

Coercion Λ_var : V >-> Λ.

Reserved Notation "M [ x ::= N ]" (at level 10).

Fixpoint Λ_subst (M:Λ) (x:V) (N:Λ) : Λ :=
  match M with
  | Λ_var v     => if (beq_nat x v) then N else M
  | Λ_abs v  M' => if (beq_nat x v) then M else Λ_abs v (M'[x ::= N])
  | Λ_app M1 M2 => Λ_app (M1[x ::= N]) (M2[x ::= N])
  end

where "M [ x ::= N ]" := (Λ_subst M x N).

Reserved Notation "M [ x ::== N ]" (at level 10).

Fixpoint Λ_subst_STRONG (M:Λ) (x:V) (N:Λ) : Λ :=
  match M with
  | Λ_var v     => if (beq_nat_STRONG x v) then N else M
  | Λ_abs v  M' => if (beq_nat_STRONG x v) then M else Λ_abs v (M'[x ::== N])
  | Λ_app M1 M2 => Λ_app (M1[x ::== N]) (M2[x ::== N])
  end

where "M [ x ::== N ]" := (Λ_subst_STRONG M x N).

Print beq_nat_refl.

(** **** Exercise: 1 star (neutral_subst)  *)
(** Prove following lemma using beq_nat. *)
Lemma neutral_subst : ∀ (M:Λ) (x:V),
  M[x ::= x] = M.
Proof with reflexivity.
  induction M; cbn; intros.
    case_eq (beq_nat x v); intros.
      rewrite beq_nat_true_iff in H. inversion H...
      reflexivity.
    case_eq (beq_nat x v); intros.
      reflexivity.
      rewrite IHM...
    rewrite IHM1, IHM2...
Qed.

(** **** Exercise: 1 star (neutral_subst_strong)  *)
(** Prove following lemma using beq_nat_STRONG. *)
Lemma neutral_subst_strong : ∀ (M:Λ) (x:V),
  M[x ::= x] = M.
Proof with reflexivity.
  induction M; cbn; intros.
    destruct (beq_nat_STRONG x v); intros.
      subst. rewrite <- beq_nat_refl...
      rewrite <- beq_nat_false_iff in n. rewrite n...
    destruct (beq_nat_STRONG x v); intros.
      subst. rewrite <- beq_nat_refl...
      rewrite <- beq_nat_false_iff in n. rewrite n, IHM...
    rewrite IHM1, IHM2...
Qed.

(** **** Exercise: 1 star (neutral_subst_STRONG)  *)
(** Prove following lemma using beq_nat_STRONG. *)
Lemma neutral_subst_STRONG : ∀ (M:Λ) (x:V),
  M[x ::== x] = M.
Proof with reflexivity.
  induction M; cbn; intros.
    destruct (beq_nat_STRONG x v); intros.
      inversion e. 1-2: congruence.
    destruct (beq_nat_STRONG x v); intros; subst; congruence.
    rewrite IHM1, IHM2...
Qed.

End Λ_exp.

(** — What are dependent types for?
    — You can for example write a function which type says that it sorts lists.
    — Have you ever done that?
    — ...

    Now is the time. *)

Definition arg2bool2Prop {X Y:Type} (R:X→Y→bool) (x:X) (y:Y) := (R x y = true).

Notation "〈 R 〉" := (arg2bool2Prop R).

Fixpoint insert_sorted {T:Type} (le_b:T→T→bool) (x:T) (xs:list T) : list T :=
  match xs with
  | []      => [x]
  | x'::xs' => if le_b x x' then x::xs else x'::(insert_sorted le_b x xs')
  end.

Print Permutation.

(** **** Exercise: 1 star (perm_example)  *)
(** Prove following lemma. *)

Ltac perm := repeat
match goal with
    | |- Permutation (?h :: _) (_ :: ?h :: _) =>
        repeat rewrite (perm_swap h)
    | |- Permutation (?h :: _) (?h :: _) => apply perm_skip
    | |- Permutation ?l ?l => reflexivity
end.

Example perm_example : Permutation [1;2;3] [3;1;2].
Proof.
  perm.
Qed.

(** **** Exercise: 1 star (perm_example)  *)
(** Prove following lemma. *)

Require Import Recdef.

Functional Scheme insert_sorted_ind :=
  Induction for insert_sorted Sort Prop.

Lemma insert_sorted_perm {T:Type} : ∀ (le_b:T→T→bool) (x:T) (xs:list T),
  Permutation (x::xs) (insert_sorted le_b x xs).
Proof.
  intros. functional induction @insert_sorted T le_b x xs;
  rewrite <- ?IHl; perm.
Qed.

Ltac gen x := generalize dependent x.
Ltac inv x := inversion x; subst; intros.

(** **** Exercise: 1 star (insert_sorted_head)  *)
(** Prove following lemma which can be usable in next excercise. *)
Lemma insert_sorted_head {T:Type} : ∀ (ord:T→T→bool) (x x':T) (xs:list T),
  ∃ y ys, insert_sorted ord x (x'::xs) = y::ys ∧ (y=x ∨ y=x').
Proof.
  cbn; intros. case_eq (ord x x'); intro.
    exists x, (x' :: xs). auto.
    exists x', (insert_sorted ord x xs). auto.
Qed.

Definition Comparing {T:Type} (ord:T→T→bool) := 
  ∀ x y, ord x y = false → ord y x = true.

Print LocallySorted.

(** **** Exercise: 3 star (insert_sorted_sorted)  *)
(** Prove a companion lemma of insert_sorted. Note that's its weak
    specification. *)
Lemma insert_sorted_sorted {T:Type} : ∀ (le_b:T→T→bool) (x:T) (xs:list T),
  (Comparing le_b) →
  LocallySorted 〈 le_b 〉 xs →
  LocallySorted 〈 le_b 〉 (insert_sorted le_b x xs).
Proof.
  unfold Comparing; intros.
  functional induction @insert_sorted T le_b x xs;
  try constructor; auto.
    destruct xs'.
      repeat constructor. apply H. assumption.
      decompose [and or ex] (insert_sorted_head le_b x t xs'); subst;
      rewrite H1 in *; constructor; inv H0; auto.
        apply H. assumption.
Qed.

(** **** Exercise: 2 star (strong_insertion_sort)  *)
(** Define strongly specified insertion sort function. *)
Fixpoint strong_insertion_sort {T:Type} (le_b:T→T→bool)
  (ord : Comparing le_b)  (xs:list T) :
  {ys | Permutation xs ys ∧ LocallySorted 〈le_b〉 ys}.
Proof.
  destruct xs as [| h t].
    exists []. split; constructor.
    destruct (strong_insertion_sort T le_b ord t) as [t' [H1 H2]].
      exists (insert_sorted le_b h t'); split.
        rewrite <- insert_sorted_perm. apply perm_skip. assumption.
        apply insert_sorted_sorted; assumption.
Defined.