Set Implicit Arguments.
Require Import Omega.
Require Import Coq.Init.Nat.
Require Import BA.External.

Ltac rewrite_eq Eq := let E := fresh  in assert (Eq) as E by omega; rewrite E; clear E.
Ltac rewrite_eq_in Eq T := let E := fresh  in assert (Eq) as E by omega; rewrite E in T; clear E.
Tactic Notation "rewrite_eq" constr(Eq) := (rewrite_eq Eq).
Tactic Notation "rewrite_eq" constr(Eq) "in" hyp(T) := (rewrite_eq_in Eq T).

Ltac destruct_simple_pattern H P := let Eq := fresh in destruct H as P eqn:Eq ; simpl in Eq; rewrite Eq; clear Eq.
Tactic Notation "destruct_spl" constr(H) "as" simple_intropattern(P) := (destruct_simple_pattern H P).

Ltac oauto := try (omega); auto.

Lemma decision_true (X:Type) (P:Prop) (decP:dec P) (x y : X) (p:P): (if (decision P) then x else y) = x.
Proof.
  decide P.
  - reflexivity.
  - exfalso. auto.
Qed.

Lemma decision_false (X:Type) (P:Prop) (decP:dec P) (x y : X) (p:~P): (if (decision P) then x else y) = y.
Proof.
  decide P.
  - exfalso. auto.
  - reflexivity.
Qed.

Lemma complete_induction (P : nat -> Prop) : P 0 -> (forall n, (forall m, m <= n -> P m) -> (P (S n))) -> forall n, P n.
Proof.
  intros p0 pS.
  enough (forall n, forall m, m <= n -> P m).
  - intros n. apply (H n n). omega.
  - induction n; intros m L.
    + now rewrite_eq (m = 0).
    + decide (m = S n) as [D|D].
      * rewrite D. apply pS. apply IHn.
      * apply IHn. omega.
Qed.

Lemma max_le_left n m k: k <= n ->  k <= max  n m.
Proof.
  intros L.
  pose (p := (Nat.le_max_l n m)).
  omega.
Qed.

Lemma max_le_right n m k : k <= m -> k <= max n m.
Proof.
  intros L. rewrite Nat.max_comm. now apply max_le_left.
Qed.

(** * Languages 
    Language Speak for predicates, makes some things sound more naturally *)

Section Languages.

  Variable (X:Type).

  Definition Language := X -> Prop.

  Definition empty_language : Language := fun _=> False.
  Definition universal_language : Language := fun _ => True.
  
  Definition language_inclusion (P Q :Language) :=
       forall w, P w -> Q w.
  
  Definition language_eq (P Q: Language) := (forall w, P w <-> Q w).
       
  Definition language_union (P Q: Language) : Language:=  fun w => P w \/ Q w.

  Definition language_intersection(P Q: Language): Language:= fun w => P w /\ Q w.

  Definition language_complement (P : Language) :Language := fun w => ~ (P w).

  Definition language_difference (P Q : Language) : Language := fun w => P w /\ ~ Q w.

End Languages.

Arguments empty_language {X} _.
Arguments universal_language {X} _.


Notation "x <$= y"  := (language_inclusion x y) (at level 70).
Notation "x =$= y" := (language_eq x y) (at level 70).
Notation "x \$/ y" := (language_union x y) (at level 69).
Notation "x /$\ y" := (language_intersection x y) (at level 69).
Notation "x ^$~ " := (language_complement x) (at level 68).
Notation "{}" := (empty_language) (at level 20).

Hint Unfold language_intersection.
Hint Unfold language_union.
Hint Unfold language_complement.
Hint Unfold language_eq.
Hint Unfold language_inclusion.
Hint Unfold empty_language.
Hint Unfold universal_language.

Section LanguageLemmata.
  Variable X:Type.
  Variables L L_1 L_2 : Language X.

  Lemma language_empty_iff : L =$= {} <-> (forall w, ~ (L w) ).
  Proof. firstorder. Qed.

  Lemma language_universal_iff : L =$= universal_language <-> (forall w, L w).
  Proof. firstorder. Qed. 

  Lemma language_eq_iff : L_1 =$= L_2 <-> L_1 <$= L_2 /\ L_2 <$= L_1.
  Proof. firstorder. Qed.

  Lemma language_eq_symmetric: L_1 =$= L_2 <-> L_2 =$= L_1.
  Proof. firstorder. Qed.

  Lemma language_union_comm:  L_1 \$/ L_2 =$= L_2 \$/ L_1.
  Proof. firstorder. Qed.

  Lemma language_intersection_comm:  L_1 /$\ L_2 =$= L_2 /$\ L_1.
  Proof. firstorder. Qed.

End LanguageLemmata.
