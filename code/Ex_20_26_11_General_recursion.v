(** * Quicksort using Bove-Capretta, [Type] version *)

Module BoveCapretta_Type.

Require Import List.
Import ListNotations.

Require Import Nat.
Require Import Arith.Wf_nat.
Require Import Omega.

Inductive qsDom {A : Type} (leb : A -> A -> bool) : list A -> Type :=
    | qsDom_nil : qsDom leb []
    | qsDom_cons : forall (t : list A) (h : A),
        qsDom leb (filter (fun x : A => leb x h) t) ->
        qsDom leb (filter (fun x : A => negb (leb x h)) t) ->
          qsDom leb (h :: t).

Arguments qsDom_nil [A leb].
Arguments qsDom_cons [A leb t] _ _ _.

Fixpoint qs_aux {A : Type} (leb : A -> A -> bool) (l : list A)
  (H : qsDom leb l) : list A :=
match H with
    | qsDom_nil=> []
    | qsDom_cons h l r => qs_aux leb _ l ++ h :: qs_aux leb _ r
end.

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Theorem lengthOrder_wf : forall (A : Type),
    well_founded (@lengthOrder A).
Proof.
  unfold lengthOrder. intro.
  apply (@well_founded_lt_compat _ (@length A)). trivial.
Defined.

Lemma filter_length :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l as [| h t]; simpl; try destruct (f h); cbn; omega.
Qed.

Theorem qsDom_all :
  forall (A : Type) (leb : A -> A -> bool) (l : list A),
    qsDom leb l.
Proof.
  intros A leb.
  apply (well_founded_induction_type (lengthOrder_wf A)).
  destruct x as [| h t]; intros IH *; constructor.
    apply IH. unfold lengthOrder, lt. cbn. apply le_n_S, filter_length.
    apply IH. unfold lengthOrder, lt. cbn. apply le_n_S, filter_length.
Defined.

Definition qs {A : Type} (leb : A -> A -> bool) (l : list A) : list A :=
  qs_aux leb l (qsDom_all A leb l).

Definition ex := [5; 0; 1; 66; 7; 23; 4; 99; 2].
Compute qs leb [5; 0; 1; 66; 7; 23; 4; 99; 2].

End BoveCapretta_Type.

(** * Quicksort using Bove-Capretta, [Prop] version *)

Module BoveCapretta_Prop.

Require Import List.
Import ListNotations.

Require Import Nat.
Require Import Arith.Wf_nat.
Require Import Omega.

Inductive qsDom {A : Type} (leb : A -> A -> bool) : list A -> Prop :=
    | qsDom_nil : qsDom leb []
    | qsDom_cons : forall (t : list A) (h : A),
        qsDom leb (filter (fun x : A => leb x h) t) ->
        qsDom leb (filter (fun x : A => negb (leb x h)) t) ->
          qsDom leb (h :: t).

Arguments qsDom_nil [A leb].
Arguments qsDom_cons [A leb t] _ _ _.

Lemma invl :
  forall (A : Type) (leb : A -> A -> bool) (h : A) (t l : list A),
    l = h :: t -> qsDom leb l ->
      qsDom leb (filter (fun x : A => leb x h) t).
Proof.
  do 2 inversion 1; auto.
Defined.

Lemma invr :
  forall (A : Type) (leb : A -> A -> bool) (h : A) (t l : list A),
    l = h :: t -> qsDom leb l ->
      qsDom leb (filter (fun x : A => negb (leb x h)) t).
Proof.
  do 2 inversion 1; auto.
Defined.

Fixpoint qs_aux {A : Type} (leb : A -> A -> bool) (l : list A)
  (H : qsDom leb l) {struct H} : list A :=
match l  as l' return (l = l' -> list A) with
    | [] => fun _ => []
    | h :: t => (fun Heq =>
          qs_aux leb _ (invl A leb h t l Heq H) ++ h ::
          qs_aux leb _ (invr A leb h t l Heq H))
end (eq_refl l).

Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Theorem lengthOrder_wf : forall (A : Type),
    well_founded (@lengthOrder A).
Proof.
  unfold lengthOrder. intro.
  apply (@well_founded_lt_compat _ (@length A)). trivial.
Defined.

Lemma filter_length :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l as [| h t]; simpl; try destruct (f h); cbn; omega.
Qed.

Theorem qsDom_all :
  forall (A : Type) (leb : A -> A -> bool) (l : list A),
    qsDom leb l.
Proof.
  intros A leb.
  apply (well_founded_induction_type (lengthOrder_wf A)).
  destruct x as [| h t]; intros IH *; constructor.
    apply IH. unfold lengthOrder, lt. cbn. apply le_n_S, filter_length.
    apply IH. unfold lengthOrder, lt. cbn. apply le_n_S, filter_length.
Defined.

Definition qs {A : Type} (leb : A -> A -> bool) (l : list A) : list A :=
  qs_aux leb l (qsDom_all A leb l).

Definition ex := [5; 0; 1; 66; 7; 23; 4; 99; 2].
Compute qs leb [5; 0; 1; 66; 7; 23; 4; 99; 2].

End BoveCapretta_Prop.