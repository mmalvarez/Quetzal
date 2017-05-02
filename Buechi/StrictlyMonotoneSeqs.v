Set Implicit Arguments.
Require Import BA.External.
Require Import Coq.Init.Nat.
Require Import BasicDefs.
Require Import Seqs.

(** * Strictly Monotone Sequences on [nat]*)

Section StrictlyMonotoneSeqs.

  Definition s_monotone (f: Seq nat):= forall n, f n < f ( S n).

  Lemma s_monotone_id : s_monotone (fun n => n).
  Proof.
    intros n. omega.
  Qed.

  Lemma s_monotone_unbouded (f: Seq nat): s_monotone f ->
        (forall n, Sigma i, f i >= n).
  Proof.
    intros A n.
    induction n.
    - exists 0. omega.
    - destruct IHn as [n' P].
      exists (S n').
      specialize (A n').
      omega.
  Qed.

  Lemma s_monotone_unbouded_ge (f: Seq nat): s_monotone f ->
        (forall n, Sigma i, f i > n).
  Proof.
    intros A n.
    destruct (s_monotone_unbouded A n) as [i P].
    exists (S i).
    specialize (A i). omega.
  Qed.

  Lemma s_monotone_ge f: s_monotone f -> forall n, n <= f n.
  Proof.
    intros F n.
    induction n.
    - omega.
    - specialize (F n). omega.
  Qed.

  Lemma s_monotone_strict_order_preserving f k n: s_monotone f -> k < n -> f k < f n.
  Proof.
    intros F L.
      remember (n - k) as z.
      assert (n = k + z) by omega. subst n.
      induction z.
      + exfalso. omega.
      + rewrite_eq (k + S  z = S (k +  z)).
        decide (z = 0) as [D|D].
        - subst z. rewrite_eq (k+0 = k). apply F.
        - specialize (F (k +  z)).
          enough (f k < f (k +  z)) by omega.
          apply IHz; omega.
  Qed.

  Lemma s_monotone_order_preserving f k n: s_monotone f -> k <= n -> f k <= f n.
  Proof.
    intros F L.
    decide (k = n).
    - subst n. omega.
    - enough (f k < f n) by omega.
      apply  s_monotone_strict_order_preserving; oauto.
  Qed.
 
  Lemma s_monotone_order_preserving_backwards f k n: s_monotone f -> f k <= f n -> k <= n.
  Proof.
    intros F L.
    decide (k <= n).
    - auto.
    - exfalso.
      assert (n < k) as H by omega.
      apply s_monotone_order_preserving with (f:=f) in H.
      specialize (F n).
      omega.
      assumption.
  Qed.

  Lemma s_monotone_ge_zero g: s_monotone g -> g 0 > 0 -> forall n, g n > 0.
  Proof.
    intros Inc GZ. intros n.
    destruct n.
    - apply GZ.
    - enough (g (S n) >= S n) by omega. now apply s_monotone_ge.
  Qed.

  Lemma s_monotone_drop g k : s_monotone g -> s_monotone (drop k g).
  Proof.
    intros Inc n. repeat rewrite drop_correct. rewrite_eq (k + S n = S ( k + n)). apply Inc.
  Qed.

  (** Chaining strictly monotone sequences preserves strict monotonicity.*)
  Lemma compose_s_monotone f g: s_monotone f -> s_monotone g -> s_monotone (fun n => g ( f n)).
  Proof.
    intros F G.
    intros n.
    specialize (F n).
    pose (p := (s_monotone_order_preserving G F)).
    now apply s_monotone_strict_order_preserving.
  Qed.

  (** For a given function [f], fix [f 0 = 0].  This preserves strict monotonicity.*)
  Definition fix_first_zero (f:nat -> nat) := fun n => match n with 
      | 0 => 0
      | S n => f (S n) end.

  Lemma fix_first_zero_s_monotone f : s_monotone f -> s_monotone (fix_first_zero f).
  Proof.
    intros IncF n. destruct n; simpl.
    - specialize (IncF 0). omega.
    - apply IncF.
  Qed.

End StrictlyMonotoneSeqs.