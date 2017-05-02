Set Implicit Arguments.

Require Import Coq.Init.Nat.
Require Import BA.External.
Require Import BA.FinTypes.
Require Import BasicDefs.
Require Import Seqs.
Require Import SeqOperations.
Require Import NFAs.
Require Import Buechi.

Open Scope string_scope.

Hint Resolve final_state_dec.
Hint Resolve initial_state_dec.
Hint Resolve transition_dec.
Hint Resolve finType_exists_dec.

(** * Decidability of Buechi Language Emptyness *)

(** ** Decidability of Final Coaccessibility
    The existance of a valid and final run can be reduced to finding final cycles
    which again can be reduced to connectivity  *)
Section FinalCycle.
  Context {A : finType}.
  Context {aut : BuechiAut A}.

  Definition accessible s := initial_state s \/ (exists s', initial_state s' /\ connected (aut:=aut) s' s).
  Definition final_coaccessible s := exists (r : Run aut) w, valid_run r w /\ final r /\ (r 0) = s.
  Definition final_cycle (r:Run aut) w s := cyclic_path r w s /\ exists n, n <= |w| /\ final_state (r n).
  Definition final_cyclic s := exists r w, final_cycle r w s.

  (** [accessible] is decidable because existentials in finite types and connectivity are decidable *)
  Instance dec_finite_accessible (s: state aut): dec (accessible s).
  Proof.
    auto.
  Defined.

  (** [final_cyclic] can be reduced to connectivity *)
  Lemma final_cyclic_to_connected s : final_cyclic s <-> ((exists s', final_state s' /\ connected (aut:= aut) s s' /\ connected (aut:=aut) s' s)).
  Proof.
    split.
    - intros  [r [w [C [n [L F]]]]].
      destruct C as [V [B E]] eqn:H.
      destruct n.
      + exists s. repeat split.
        * now rewrite <- B.
        * apply (cyclic_path_connects C).
        * apply (cyclic_path_connects C).
      + exists (r ( S n)). repeat split; auto. 
        * rewrite <-B. apply (cyclic_path_connects_on_path C). omega.
        * rewrite <-E. apply (cyclic_path_connects_on_path C). omega.
    - intros [s' [F [C1 C2]]].
      destruct C1 as [r1 [w1 [V1 [B1 E1]]]]. destruct C2 as [r2 [w2 [V2 [B2 E2]]]].
      exists (prepend_path (|w1|) r1 r2), ( w1 ++ w2). repeat split.
      + apply prepending_path_on_path_is_valid; auto. now rewrite B2, E1.
      + rewrite prepend_path_begin_correct; oauto.
      + simpl. rewrite_eq ( (S ((| w1 |) + S (| w2 |))) = S(|w1|) + S(|w2|)).
        now rewrite prepend_path_rest_correct.
      + exists (S(|w1|)). split.
        * simpl. omega.
        * rewrite_eq (S(|w1|) = S(|w1|) + 0).
          rewrite prepend_path_rest_correct. now rewrite B2.
  Qed.

  Instance dec_final_cyclic s : dec (final_cyclic s).
  Proof.
    apply (dec_prop_iff (X:=(exists s', final_state s' /\ connected (aut:= aut) s s' /\ connected (aut:=aut) s' s))).
    - symmetry. apply final_cyclic_to_connected.
    - auto.
  Qed.
  
  (** Every final and valid run has a final cycle *)
  Lemma final_valid_run_has_cycle r w: valid_run r w -> final r -> exists (s : state aut), connected (r 0) s /\ exists r' w', final_cycle r' w' s.
  Proof.
    intros V [s [Inf Fin]].
    destruct (Inf 1) as [m1 [P1 Q1]].
    destruct (Inf (S m1)) as [m2 [P2 Q2]].
    exists s. split.
    - exists r, (mkstring w (pred m1)). repeat split.
      + apply (valid_run_is_path_from_begin V).
      + simpl. now rewrite_eq (S(pred m1) = m1).
    - exists (drop m1 r), (extract m1 m2 w). repeat split.
      + apply (valid_run_is_path_everywhere V).
      + rewrite drop_correct. now rewrite_eq (m1+0 = m1).
      + rewrite drop_correct. simpl. now rewrite_eq (m1 + S (m2 - S m1) = m2).
      + exists 0. split.
        * omega.
        * rewrite drop_correct. rewrite_eq(m1 + 0 = m1). now rewrite Q1.
  Qed. 

  (** [final_coaccessible] can be reduced to what we already have *)
  Lemma final_coaccessible_iff_final_cycle s:
     final_coaccessible s <-> (exists s', connected s s' /\ final_cyclic s').
  Proof.
  split.
  - intros [r [w [V [F I]]]].
    rewrite <-I.
    now apply (final_valid_run_has_cycle V).
  - intros [s' [[r [w C]] [r' [w' [C' F']]]]].
    pose (r2 := (mkstring r' (|w'|)) to_omega).
    pose (w2 := w' to_omega).
    pose (r1 := (mkstring r (|w|)) +++ r2).
    pose (w1 := w +++ w2).
    exists r1, w1. repeat split; unfold r1,w1,r2,w2; simpl.
    + apply prepending_path_is_valid.
      * apply C.
      * simpl. destruct C as [_ [_ C]]; destruct C' as [_ [C' _]].
        now rewrite C, C'.
      * apply (non_empty_cycle_is_valid C').
    + destruct F' as [n [L F]].
      exists (r' n). split.
      * apply finite_prefix_preserves_infinite.
        now apply omega_iteration_infinite.
      * assumption.
    + rewrite prepend_path_begin_correct by omega.
      now destruct C as [_ [C _]].
  Qed.

  Instance dec_final_coaccessible s: dec (final_coaccessible s).
  Proof.
    apply (dec_prop_iff (X:= exists s', connected s s' /\ final_cyclic s')).
    - split; apply final_coaccessible_iff_final_cycle.
    - auto.
  Defined.

End FinalCycle.


(** ** Trimming of NFAs w.r.t. Buechi Languages
    The trim automaton only consists of the trim states, but it recognizes the same language. *)
Section TrimAutomata.
  
  Context {A : finType}.
  Context {aut: BuechiAut A}.

  Definition state_trim (s:state aut):= accessible s /\ final_coaccessible s.

  Hint Resolve dec_finite_accessible.
  Hint Resolve dec_final_coaccessible.
  Hint Resolve and_dec.

  Lemma dec_state_trim s : dec (state_trim s).
  Proof.
    unfold state_trim. auto.
  Qed.
  
  Definition trim_state := finType_sub state_trim dec_state_trim.
  Definition orig_state (s:trim_state) : (state aut):= match s with
     exist _ s _ =>s end.

  Definition trim_transition s a s':=  transition (orig_state s) a (orig_state s').
  Definition trim_initial s := initial_state (orig_state s).
  Definition trim_final s := final_state (orig_state s).

  Lemma dec_trim_transition s a s': dec(trim_transition s a s'). Proof. auto. Qed.
  Lemma dec_trim_initial s: dec(trim_initial s). Proof. auto. Qed.
  Lemma dec_trim_final s : dec (trim_final s). Proof. auto. Qed.  
   
  Definition trim_aut := mknfa dec_trim_transition dec_trim_initial dec_trim_final.

  (** ***  Trim automaton recognizes the same language *)

  Lemma trim_accepted_by_aut: L_B trim_aut <$= L_B aut.
  Proof.
    intros w [r [V [I [s [Inf Fin]]]]].
    exists (seq_map orig_state r). repeat split; auto.
    exists (orig_state s). 
    destruct s as [s' p]. simpl. split.
    - intros n. destruct (Inf n) as [m [P Q]].
      exists m. split;auto.
      unfold seq_map. now rewrite Q.
    - auto.
  Qed.

  Lemma states_in_final_path_are_trim r w: valid_run r w -> final r -> initial r -> forall n, state_trim (r n).
  Proof.  
    intros V F I n.
    unfold state_trim. split.
    - unfold accessible. destruct n.
      + now left.
      + right.  exists (r 0). split; auto.
        apply (valid_run_connects V). omega.
    - exists (drop n r); exists (drop n w). repeat split. 
      + now apply (valid_run_drop ).
      + now apply final_drop.
      + rewrite drop_correct. now f_equal.
  Qed.   

  Lemma states_trim_subtype s n r w: valid_run r w -> final r -> initial r -> s = r n ->
    pure state_trim (D:= dec_state_trim) s.
  Proof.
   intros V F I E.
   unfold pure.
   rewrite E.
   decide (state_trim (r n)). split.
   - apply n0. now apply (states_in_final_path_are_trim V) .
  Qed.

  Lemma aut_accepted_by_trim: L_B aut <$= L_B trim_aut.
  Proof.
  intros w [r [V [I F]]].
  pose (MkTrim:= fun s k (N: s = r k) => exist (pure state_trim (D:= dec_state_trim)) s 
        (states_trim_subtype  V F I N ): subtype state_trim ).
  exists (seq_map (fun n => MkTrim (r n) n eq_refl ) (fun n => n)).

  destruct (final_valid_run_has_cycle V F) as [s [C [k [r' [w' K]]]]].

  repeat split; auto.
  unfold final.
  destruct F as [f [Inf Fin]]. destruct (Inf 0) as [nf [Pf Qf]].
  symmetry in Qf.
  exists (MkTrim f nf Qf). split.
  - intros n. destruct (Inf n) as [m [P Q]].
    exists m. split;auto.
    unfold MkTrim, seq_map. f_equal.
    destruct Q.
    f_equal.
    apply pure_eq.
  - apply Fin.
  Qed.
  
  Lemma trim_accepts_same_as_aut: L_B aut =$= L_B trim_aut.
  Proof.
  split.
   - apply aut_accepted_by_trim.
   - apply trim_accepted_by_aut.
  Qed.
  
  (** *** Decidability of language emptiness of a trim automaton
      The Buechi language of a trim automaton is empty iff it has no states *)
  Definition trim (aut:BuechiAut A):= forall (s: state aut), accessible s /\ final_coaccessible (A:=A)  s.
  
  Lemma trim_state_implies_language_non_empty: state trim_aut -> exists w, (L_B aut) w.
  Proof.
   intros [s P].
   rewrite <-pure_equiv in P.
   destruct P as [[I | [s' [I  [r' [w' [V' [r'0 r's]]]]]]] [r [w [V [F rs]]]]].
   - exists w, r. repeat split; auto. unfold initial. now rewrite rs.
   - exists (w' +++ w), (mkstring r' (|w'|) +++  r). repeat split; simpl.
     + apply prepending_path_is_valid; auto.
       now rewrite rs, r's.
     + unfold initial. rewrite prepend_path_first.
       now rewrite r'0.
     + now apply final_prepend.
  Qed.

  Lemma trim_empty_buechi : (~exists (s: state trim_aut), True) <-> L_B aut =$= {}.
  Proof.
    split.
    - intros E. apply language_empty_iff. intros w LA. apply E.
      pose (Q:= trim_accepts_same_as_aut). autounfold in Q.
      rewrite Q in LA.
      destruct LA as [r _]. now exists (r 0).
    - intros LA [r _]. 
      destruct (trim_state_implies_language_non_empty r) as [w Lw].
      specialize (LA w). now apply LA.
  Qed.
   
  Instance dec_trim_states_empty: dec (exists (s :state trim_aut), True).
  Proof. auto. Defined.

  (** *** Informative Decision of Buechi Language Emptiness *)
  Theorem dec_language_empty_informative : {exists w, L_B aut w} + {L_B aut =$= {}}.
  Proof.
    decide (exists (s: state trim_aut), True) as [D|D].
    - left. destruct D. now apply trim_state_implies_language_non_empty.
    - right. now apply trim_empty_buechi.
  Qed.

  Corollary dec_language_empty: dec(L_B aut =$= {}).
  Proof.
    destruct dec_language_empty_informative as [D|D].
    - right. intros E. destruct D as [w Lw]. now apply (E w).
    - now left.
  Qed. 
End TrimAutomata.

