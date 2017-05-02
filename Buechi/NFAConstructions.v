 Set Implicit Arguments.

Require Import Coq.Init.Nat.
Require Import Coq.Relations.Relation_Definitions.
Require Import BA.External.
Require Import BA.FinTypes.

Require Import Seqs.
Require Import BasicDefs.
Require Import StrictlyMonotoneSeqs.
Require Import SeqOperations.
Require Import NFAs.
Require Import Buechi.
Require Import Utils.

Hint Resolve transition_dec.
Hint Resolve final_state_dec.
Hint Resolve initial_state_dec.
Hint Resolve finType_exists_dec.


Open Scope string_scope.

(** * Constructions on NFAs
    We show constructions combinition string and Buechi languages of NFAs *)

(** ** General Facts of Infinite Concattenation and Prepending of Runs and Sequences on NFAs *)
Section ConcatInfPrependNFA.
  
  Context {A:finType}.
  Context {aut: BuechiAut A}.

  (** *** Facts that Infinite Concattenation or Prepending are Valid and Buechi Final *)
  
  (** Prepending a string to a sequence and a valid run for the string on valid run of the sequence is
      valid if they agreee at the common state *)
  Lemma prepend_string_is_valid r0 w0 r w:  |r0| = |w0| -> valid_path (seq r0) w0 -> r0 [S (|r0|)] = r 0 
                      ->  valid_run (aut:=aut) r w -> valid_run (r0 +++ r) (w0 +++ w).
  Proof.
    intros e v a V.
    rewrite e. apply prepending_path_is_valid; auto.
    now rewrite <-e.
  Qed. 

  (** Show that the infinite concattenation of strings is valid if the runs agree on the shared state *)
  Variable strings: Seq (String A).
  Variable runs: Seq (String (state aut)).

  Lemma concat_inf_is_valid:
        (forall n, |strings n| = |runs n| /\ valid_path (seq(runs n)) (strings n) /\ (runs n)[S(|runs n|)] = (runs (S n)) [0])
        -> valid_run (concat_inf runs) (concat_inf strings).
  Proof.
    intros V n. unfold concat_inf.
    rewrite (concat_inf_index_equal (f:= strings) (f':= runs)) by apply V.
    destruct (concat_inf_indices runs n) as [wi ni] eqn:H.
    destruct (concat_inf_index_step_correct H) as [H' | [H'1 H'2]].
    - rewrite H'. simpl. apply V.
      rewrite <-(concat_inf_index_equal (f:= strings) (f':= runs)) in H by apply V.
      apply (concat_inf_index_in_bounds H).
    - rewrite H'1, H'2. simpl. 
      destruct (V wi) as [L [V' B]].
      rewrite <-B. apply V'. omega.
  Qed.

  Definition visits_final (r: String (state aut)):= exists k, k <= | r| /\ final_state (r [k]).

  (** Using (A1) it suffices that there are infinitely many strings, which visit a final state,
      such that the infinite concattenation is final *)
  Lemma concat_inf_is_final_not_constructive:
     (forall n, exists m, m >= n /\ visits_final (runs m)) -> final (concat_inf runs).
  Proof.
   intros F.
   apply infinite_final_is_accepting_for_finite_automaton.
   intros n. destruct (F n) as [m [L [k [L' Fin]]]].
   exists ((begin_in runs m) + k). split.
   - enough (begin_in runs m >= m) by omega.
     apply (s_monotone_ge).
     apply s_monotone_begin_in.
   - now rewrite concat_inf_correct.
  Qed.

  Lemma concat_inf_final_step r0 : 
     final (concat_inf runs) -> final (r0+++ concat_inf runs).
  Proof.
   intros [s [Inf Fin]].
   exists s. split; auto.
   intros n. destruct (Inf n) as [m [P Q]].
   exists (m + S (|r0|)). split.
   - omega.
   - rewrite_eq (m + S(|r0|) = S(|r0|) + m).
     now rewrite prepend_path_rest_correct.
  Qed.

  (** Now show the other direction: if the infinite concattenation is final, then there are infinitely
      many strings visiting a final state *)
  Lemma final_concat_inf_infinite_final_strings: final(concat_inf runs) -> forall n, exists m, m >= n /\ visits_final (runs m).
  Proof.
    intros [s [Inf Fin]] n.
    destruct (Inf (begin_in runs n)) as [m [P Q]].
    unfold concat_inf in Q.
    destruct (concat_inf_indices runs m) as [w i]eqn:H.
    simpl in Q.
    exists w. split.
    - decide (m = begin_in runs n).
      + subst m. rewrite concat_inf_index_begin in H.
        enough (w = n) by omega. congruence.
      + assert (begin_in runs n < m) as D by omega.
        pose (Z:=concat_inf_index_le runs D).
        rewrite concat_inf_index_begin,H in Z.
        unfold nat_pair_le in Z. simpl in Z. omega.
    - unfold visits_final. exists i. split.
      + apply (concat_inf_index_in_bounds H).
      + now rewrite Q.  
  Qed.

  (** *** Facts showing that Composing the Sequence carry over to the Run *)

  (** If the sequence is obtained by prepending, we can split the run accordingly. *)
  Lemma partition_run_on_prepend_string w0 w r : valid_run (aut:=aut) r (w0 +++ w) ->
     exists r0 r', (forall n, (r0 +++ r') n = r n) /\ (|r0| = |w0|) /\ (r0 [S(|r0|)] = r' 0) /\ valid_path  (seq r0) w0 /\ valid_run r' w.
  Proof.
   intros V.
   exists (mkstring r (|w0|)); exists (drop (S(|w0|)) r). repeat split.
   - intros n.  decide (n <= (|w0|)).
     + now rewrite prepend_path_begin_correct.
     + rewrite_eq (n = S(|w0|) + (n - S(|w0|))).
       rewrite prepend_path_rest_correct.
       now rewrite drop_correct.
   - rewrite drop_correct. simpl. f_equal. omega.
   - simpl. apply (valid_path_extensional (w:= mkstring (prepend_path (| w0 |) w0 w) (|w0|))).
     + now apply valid_run_is_path_from_begin.
     + split; simpl; auto. intros n L . now rewrite prepend_path_begin_correct.
   - apply (valid_run_extensional (r := (drop (S (| w0 |)) r)) (w:= drop (S(|w0|)) (prepend_path (| w0 |) w0 w))).
     + now apply valid_run_drop. 
     + auto.
     + intros n. apply revert_prepend_path.
  Qed.    

  (** Likewise, if the sequence was obtained by infinite concattenation, the run can be partitioned
      into infinitely many strings *)
  Lemma partition_run_on_concat_inf W r : valid_run (aut:=aut) r (concat_inf W) ->
     exists R, (forall n, concat_inf R n = r n) /\
        (forall k, |R k| = |W k| /\ valid_path (seq (R k)) (W k)) /\
         (forall k, (R k)[ S(|R k|)] = (R (S k)) [0]) .
  Proof.
    intros V.
    exists (fun n => extract (begin_in W n) (begin_in W (S n)) r). repeat split.
    - intros n.
      unfold concat_inf.
      destruct (concat_inf_indices) as [w i] eqn:H.
      simpl. rewrite drop_correct.
      apply concat_inf_index_to_begin in H.
      destruct H as [H _]. rewrite  H. f_equal.
      assert (forall n, begin_in (fun n => extract (begin_in W n) (begin_in W (S n)) r) n = begin_in W n) as H'. {
        intros k. induction k.
        - reflexivity.
        - simpl in IHk. simpl. rewrite IHk. omega. }
      now rewrite <-H'.
    - simpl. omega.
    - simpl. intros n L.
      repeat rewrite drop_correct.
      rewrite <-concat_inf_correct by auto.
      rewrite_eq ((begin_in W k + S n) = S(begin_in W k +  n)).
      now apply V.
    - intros k.
      simpl. repeat rewrite drop_correct.
      f_equal. omega.
  Qed.
   
End ConcatInfPrependNFA.

Instance dec_visits_final (alphabet:finType) (aut: BuechiAut alphabet) r : dec(visits_final (aut:=aut) r).
Proof. (* Follows from decidability of bounded existentials on nat *)
  unfold visits_final. auto.
Qed.


(** * Normalization of NFAs regarding String Languages *)
(** _Warning_
    
    By now, you enter ugly code. I have not spend time on beautifing it because
    it shows results which are a) well known and b) carry over to constructive logic without
    conceptually difficulties.We will only need the last lemma for the complementation. *)

Section NormalizeNFA.

  Context {A:finType}.
  Variable (aut:NFA A).

  Definition special_states := finType_bool.
  Notation "'Initial'" := false.
  Notation "'Final'" := true.


  Definition norm_state := (state aut) (+) special_states.
  Definition norm_initial_state (s:norm_state):= s = inr (Initial).
  Definition norm_final_state (s:norm_state) := s = inr(Final).
  Definition norm_transition (s:norm_state) (a:A) (s':norm_state) := match s, s' with
   | inl s, inl s'  => transition s a s'
   | inr Initial, inl s' => exists s, initial_state s /\ transition s a s'
   | inl s , inr Final => exists s', final_state s' /\ transition s a s'
   | inr Initial, inr Final => exists (s s':state aut), initial_state s /\ final_state s' /\ transition s a s'
   | _, _ => False
  end.
  
  Instance dec_norm_initial_state s: dec (norm_initial_state s). Proof. auto. Defined.
  Instance dec_norm_final_state s: dec (norm_final_state s). Proof. auto. Defined.
  Instance dec_norm_transition s a s' : dec (norm_transition s a s').
  Proof.
   destruct s as [s | [|]]; destruct s' as [s' | [|]]; simpl; auto using and_dec.
  Qed.

  Definition norm_aut := mknfa dec_norm_transition dec_norm_initial_state dec_norm_final_state.
  
  Lemma first_norm_is_initial (r:Run norm_aut) : sinitial r -> (r 0) = inr Initial.
  Proof.
    intros I.
    unfold sinitial in I.
    simpl in I.
    now unfold norm_initial_state in I.
  Qed.
  
  Lemma last_norm_is_final (r: Run norm_aut) w : sfinal r w -> (r (S(|w|))) = inr Final.
  Proof.
    intros F.
    unfold sfinal in F.
    simpl in F.
    now unfold norm_final_state in F.
  Qed.

  Lemma other_norm_is_aut_state (r: Run norm_aut) w : svalid r w -> forall n, 1 <= n <= |w| -> exists s, r n = inl s.
  Proof.
    intros V n L.
    induction n.
    - exfalso. omega.
    - assert (norm_transition (r n) (w [n]) (r (S n))) as Sn. {apply (V n). omega. }
      decide (S n = 1) as [D|D].
      + destruct(r (S n)) as [sn |[|]] eqn:E.
        * now exists sn.
        * exfalso.
          assert (norm_transition (r (S n)) (w [S n]) (r (S (S n)))) as SSn. { apply (V (S n)). omega. }
          rewrite E in SSn.
          destruct (r (S (S n))) as [? | [|]]; simpl in SSn; contradiction SSn.
        * exfalso.
          destruct (r n) as [? | [|]]; simpl in Sn; contradiction Sn.
      + assert (1 <= n <= |w|) as H by omega.
        destruct (IHn H) as [s Es].
        rewrite Es in Sn. simpl in Sn.
        destruct (r (S n)) as [sn | [|]] eqn:E.
        * now exists sn.
        * exfalso.
          assert (norm_transition (r (S n)) (w [S n]) (r (S (S n)))) as SSn. { apply (V (S n)). omega. }
          rewrite E in SSn.
          destruct (r (S (S n))) as [? | [|]]; simpl in SSn; contradiction SSn.
        * contradiction Sn.
  Qed.

  Lemma aut_accepts_norm_aut: L_S norm_aut <$= L_S aut.
  Proof.
    intros w [r [V [I F]]].
    decide (|w| = 0) as [D|D].
    -  pose (S0 := (V 0)).
       rewrite first_norm_is_initial in S0 by auto.
       rewrite_eq (1 = S(|w|)) in S0.
       rewrite last_norm_is_final in S0 by auto.
       assert (0 <= |w|) as H by omega.
       specialize (S0 H).
       simpl in S0.
       destruct S0 as [s0 [s1 [Is0 [Fs1 T]]]].
       exists (fun n => match n with
                | 0 => s0
                | 1 => s1
                | n => s0 end).
       repeat split.
       + unfold svalid.
         intros n L.
         now rewrite_eq (n = 0).
       + now unfold sinitial.
       + unfold sfinal. now rewrite D.
    -  pose (S0 := (V 0)).
       rewrite first_norm_is_initial in S0 by auto.
       assert (0 <= |w|) as H by omega.
       specialize (S0 H).
       assert (1 <= 1 <= |w|) as H1 by omega.
       destruct (other_norm_is_aut_state V H1) as [s1 P1].
       rewrite P1 in S0.
       simpl in S0.
       destruct S0 as [s0 [Is0 T0]].

       pose (Sw := (V (|w|))).
       rewrite last_norm_is_final in Sw by auto.
       assert (|w|<= |w|) as Hw by omega.
       specialize (Sw Hw).
       assert (1 <= |w| <= |w|) as Hw' by omega.
       destruct (other_norm_is_aut_state V Hw') as [sw Pw].
       rewrite Pw in Sw.
       simpl in Sw.
       destruct Sw as [sSw [FsSw Tw]].

       exists (fun n => if (decision (n = 0))
                          then s0
                          else if  (decision (n = S(|w|)))
                              then sSw
                              else match (r n) with
                                 |inl s => s
                                 |inr b => s0 
                                 end
                             ).
       repeat split.
       + intros n L.
         decide (n = 0) as[D0|D0].
         * rewrite D0. repeat rewrite decision_false by omega. now rewrite P1.
         * repeat rewrite decision_false by omega.
           assert (1<=n<=|w|) as Hn by omega.
           destruct (other_norm_is_aut_state V Hn) as [sn Pn].
           rewrite Pn.
           decide (S n = S (|w|)).
           -- assert (n = |w|) as NW by omega. subst n.
              rewrite Pn in Pw.  congruence.
           -- assert (1 <= S n <= |w|) as HSn by omega.
              destruct (other_norm_is_aut_state V HSn) as [sSn PSn].
              rewrite PSn.  specialize (V n L).
              now rewrite PSn, Pn in V.
       + unfold sinitial. now rewrite decision_true by omega.
       + unfold sfinal.
         rewrite decision_false by omega.
         now rewrite decision_true by omega.
   Qed.


   Lemma norm_aut_accepts_aut: L_S aut <$= L_S norm_aut.
   Proof.
     intros w [r [V [I F]]].
     exists (fun n => if (decision (n = 0))
                       then inr Initial
                       else if (decision (n = S (|w|)))
                         then inr Final
                         else inl (r n)). 
     repeat split.
     - intros n L.
       decide (n = 0).
       + rewrite decision_false by omega. 
         decide (S n = S (|w|)).
         * simpl. exists (r 0); exists (r 1). repeat split.
           -- apply I.
           -- rewrite_eq (1 = S (|w|)). apply F.
           -- rewrite_eq (n = 0). apply V. omega.
         * simpl. exists (r 0). repeat split.
           -- apply I.
           -- rewrite_eq (n = 0). apply V. omega.
       + repeat rewrite decision_false by omega.
         decide (S n = S (|w|)).
         * simpl. exists (r (S (|w|))). repeat split.
           -- apply F.
           -- rewrite_eq (S(|w|) = S n). apply V. omega.
         * simpl. apply V. omega.
     - unfold sinitial. now rewrite decision_true by omega.
     - unfold sfinal.
       rewrite decision_false by omega.
       now rewrite decision_true by omega.
   Qed.

   Definition sautomaton_normalized (aut: NFA A) (initialS finalS : state aut):= 
        (initial_state initialS /\ (forall s, initial_state s -> s = initialS) /\ (forall s a, ~ transition (aut:=aut) s a initialS)) /\
        (final_state finalS /\ (forall s, final_state s -> s = finalS) /\ (forall a s, ~transition (aut:=aut) finalS a s)).
   Arguments sautomaton_normalized  _ _ _ : clear implicits.
  
   Theorem normalize_aut: Sigma norm_aut initialS finalS, L_S aut =$= L_S norm_aut /\ sautomaton_normalized norm_aut initialS finalS.
   Proof.
     exists (norm_aut); exists (inr Initial); exists (inr Final).
     split.
     - intros w. split.
       + apply norm_aut_accepts_aut.
       + apply aut_accepts_norm_aut.
     - repeat split; auto.
       intros s a T.
       simpl in T. unfold norm_transition in T.
       destruct s as [s |[|]]; auto.
   Qed.      
End NormalizeNFA.   

(** * #&omega;#-Iteration of a NFA String Language *)
Section W_Omega_Automata.
  Context {alphabet:finType}.
  
  Variable (autW: NFA alphabet).
  Variables (initialW finalW : state autW).

  Variable (normW: sautomaton_normalized initialW finalW).

  Definition Womega_transition s a s' := (s' <> initialW /\ transition s a s') \/ (s' = initialW /\ transition s a finalW).
  Definition Womega_state_final s := s = initialW.
  Definition Womega_state_initial s := s = initialW. 

  Instance dec_Womega_transition s a s' : dec (Womega_transition s a s'). Proof. unfold Womega_transition. auto. Qed.
  Instance dec_Womega_state_final s : dec (Womega_state_final s). Proof. auto. Qed.
  Instance dec_Womega_state_initial s : dec (Womega_state_initial s). Proof. auto. Qed.

  Definition Womega_aut := mknfa dec_Womega_transition dec_Womega_state_initial dec_Womega_state_final.

  Lemma finalW_does_not_appear_in_valid_run r w: valid_run r w -> forall n, r n <> finalW.
  Proof.
    intros V n. specialize (V n).
    decide (r n = finalW) as [D|D].
    - exfalso. rewrite D in V. destruct normW as [_ [_ [_ nF]]]. now apply (nF (w n) (r (S n))).
    - assumption.
  Qed.


  Lemma compute_run w: (L_S autW w) -> Sigma r, saccepting (aut := autW) r w.
  Proof.
    intros W.
    decide (exists (r : (state autW) ^ (finType_Le_K (S (|w|)))), saccepting (aut:=autW) (to_seq r) w) as[D|D].
    - apply finType_cc in D; auto.
      destruct D as [r A].
      exists (to_seq r); auto.
    - exfalso. apply D.
      destruct W as [r A].
      exists (to_bounded r). repeat split.
      + unfold svalid. intros n L. repeat rewrite bounded_unchanged by omega. now apply A.
      + unfold sinitial. rewrite bounded_unchanged by omega. apply A.
      + unfold sfinal. rewrite bounded_unchanged by omega. apply A.
  Qed.     

  Lemma aut_accepts_w_omega: (L_S autW)^00  <$= L_B Womega_aut.
  Proof.
    intros w W.
    apply o_iter_implies_o_iter2 in W.
    destruct W as [ws [W C]].
    (* Need to do this nasty case distinction even though this index does not contribute to the concatted string to 
       be able to apply the lemma concat_inf_is_valid *)
    pose (R:= fun (n:nat) => mkstring (fun k => if (decision (k = S (|ws n|))) then initialW else (projT1 (compute_run (W n))) k) (|ws n|) : String (state Womega_aut)).
    exists (concat_inf R).
    repeat split.
    - apply (valid_run_extensional (w:= concat_inf ws) (r := (concat_inf R))).
      + apply concat_inf_is_valid. repeat split.
        * unfold R. destruct (compute_run (W n)) as [r [Vn [In Fn]]].  simpl.
          unfold svalid in Vn. simpl in Vn. intros k L. simpl. unfold Womega_transition.
          unfold sfinal in Fn.
          decide (k = |ws n|).
          -- subst k. destruct normW as [_ [_ [N _]]]. specialize (N (r (S (| ws n |))) Fn).
             decide (finalW = initialW) as [D|D].
             ++ right. split.
                ** now rewrite decision_true by omega.
                ** rewrite decision_false by omega.
                   rewrite <-N. apply Vn. omega.
             ++ rewrite decision_true by omega. right.
                rewrite decision_false by omega.
                split; auto. 
                rewrite <-N. apply Vn. omega.
          -- left. split.
             ++ specialize (Vn k).
                destruct normW as [[_ [_ I]] _ ].
                decide (r (S k) = initialW) as [D|D].
                ** exfalso. rewrite D in Vn. apply (I (r k) ((ws n) [k])). apply Vn. omega.
                ** rewrite decision_false by omega. assumption.
             ++ repeat rewrite decision_false by omega. now apply Vn.  
         * unfold R. destruct (compute_run (W n)) as [r [V [I F]]]; destruct (compute_run (W (S n))) as [r' [V' [I' F']]]. simpl.
           unfold sinitial in I'. apply normW in I'. rewrite I'.
           unfold sfinal in F. apply normW in F.
           rewrite decision_true by omega.
           now rewrite decision_false by omega.
      + auto.
      + intros n. symmetry. apply C.
    - unfold initial, concat_inf. simpl.
      destruct (compute_run (W 0)) as [r [V [I F]]]. simpl.
      unfold Womega_state_initial. unfold sinitial in I.
      rewrite decision_false by omega.
      now apply normW in I.
    - exists (initialW). split.
      + intros n. exists (begin_in R n). split.
        * apply s_monotone_ge. apply s_monotone_begin_in.
        * unfold concat_inf. rewrite concat_inf_index_begin. simpl.
          destruct (compute_run (W n)) as [r [V [I F]]]. simpl.
          rewrite decision_false by omega.
          now apply normW in I.
      + reflexivity.
  Qed.

  Lemma initialW_partitions_in_W r w n m: accepting (aut:=Womega_aut) r w 
               -> n < m -> r n = initialW -> r m = initialW 
               -> (forall k, n < k < m -> r k <> initialW )
                    -> (L_S autW) (extract n m w).
  Proof.
    intros [V [I F]] L nW mW kNW.
    exists ((extract n m r) +++ (fun _ => finalW)).
    repeat split.
    - intros k B. simpl.
      decide (k < m - S n).
      + repeat rewrite prepend_path_begin_correct by omega.
        repeat rewrite drop_correct. rewrite_eq (n + S k = S(n+k)).
        specialize (V (n + k)). simpl in V. unfold Womega_transition in V.
        destruct V as [[_ V] | [V _]].
        * assumption.
        * exfalso. apply (kNW (S (n + k))); oauto.
      + decide (k = m - S n).
        * rewrite prepend_path_begin_correct by omega.
          rewrite_eq (S k = S (m - S n) + 0).
          rewrite prepend_path_rest_correct by omega.
          specialize (V (n + k)). simpl in V. unfold Womega_transition in V.
          destruct V as [[V _] | [_ V]].
          -- exfalso. apply V. now rewrite_eq (S (n + k ) = m).
          -- now repeat rewrite drop_correct.
        * simpl in B. exfalso. omega. 
    - unfold sinitial. simpl. rewrite prepend_path_begin_correct by omega.
      rewrite drop_correct. rewrite_eq ( (n + 0) = n).
      rewrite nW. apply normW.
    - unfold sfinal. simpl.
      rewrite_eq (S (m - S n) =S (m - S n) + 0).
      rewrite prepend_path_rest_correct by omega.
      apply normW.
  Qed.

  Arguments infinite_filter [X] _ _ _ _ _. 

  Lemma aut_is_w_omega: L_B Womega_aut <$= (L_S autW)^00.
  Proof.
    intros w [r A].
    pose (A' := A). destruct A' as [V [I [s [Inf Fin]]]].
    simpl in Fin. unfold Womega_state_final in Fin. subst s.
    exists (infinite_filter r (fun s => s = initialW) (fun s=> decision (s = initialW)) Inf). repeat split.
    - apply infinite_filter_s_monotone.
    - apply infinite_filter_zero. apply I.
    - intros n. apply (initialW_partitions_in_W A).
      + apply infinite_filter_s_monotone.
      + apply infinite_filter_correct.
      + apply infinite_filter_correct.
      + apply infinite_filter_all.
  Qed.

  Lemma w_omega_aut_correct: L_B Womega_aut =$= (L_S autW)^00.
  Proof.
    split.
    - apply  aut_is_w_omega.
    - apply aut_accepts_w_omega.
  Qed.

  Lemma w_omega_one_initial_state: initial_state (aut:=Womega_aut) initialW /\ final_state (aut:=Womega_aut) initialW /\ 
                                   (forall (s: state Womega_aut), initial_state s -> s = initialW) /\
                                   forall (s: state Womega_aut), initial_state s -> s = initialW.
  Proof.
    repeat split; simpl; auto.
  Qed.
End W_Omega_Automata.

(** * Prepending a String on a Buechi Language *)  
Section PrependFinLanguage_Automata.

  Context {alphabet:finType}.
  
  Variable (autV : NFA alphabet).
  Variables (initialV finalV : state autV).
  Variable (normV: sautomaton_normalized initialV finalV).

  Variable (autW: BuechiAut alphabet).
  Variable (initialW : state autW).
  Variable (normW : initial_state initialW /\ final_state initialW /\  (forall (s : state autW), initial_state s -> s = initialW )/\  forall s, final_state s -> s = initialW).

  Definition vw_state := (state autV) (+) (state autW).

  Definition vw_transition (s:vw_state) (a:alphabet) (s' : vw_state) := match s,s' with
      | inl s, inl s' => transition (aut:=autV) s a s' /\ s' <> finalV
      | inl s, inr s' => transition (aut:=autV) s a finalV /\ s' = initialW
      | inr s, inr s' => transition (aut:=autW) s a s'
      | inr _, inl _  => False
  end.

  Definition vw_state_final (s:vw_state) := s = inr initialW.
  Definition vw_state_initial (s:vw_state) := s = inl initialV.

 
  Instance dec_vw_transition s a s': dec (vw_transition s a s'). Proof. destruct s,s'; simpl; auto. Qed.
  Instance dec_vw_state_final s : dec (vw_state_final s). Proof. auto. Qed.
  Instance dec_vw_state_initial s : dec (vw_state_initial s). Proof. auto. Qed.

  Definition vw_aut := mknfa dec_vw_transition dec_vw_state_initial dec_vw_state_final.

  Arguments can_find_next_position [X] _ _ [w] [n] [m] _ _.

  Lemma initialW_always_final r w: accepting (aut:=vw_aut) r w-> infinite (inr initialW) r.
  Proof.
    intros [_ [_ [s [Inf F] ]]].
    simpl in F. unfold vw_state_final in F.
    now subst s.
  Qed.

  Lemma there_is_initialW r w: accepting (aut:=vw_aut) r w-> {k| r k = inr initialW}.
  Proof.
    intros A. apply cc_nat.
    - intros n. decide (r n = inr initialW). left; auto. right. auto.
    - destruct (initialW_always_final A 0) as [x P]. now exists x.
  Qed.

  Lemma switch_from_V_to_W r w : accepting (aut:=vw_aut) r w -> Sigma k, k > 0 /\ r k = inr initialW /\(forall n, n < k -> exists s, r n = inl s) /\ (forall n, n >= k -> exists s, r n = inr s).
  Proof.
    intros A.
    destruct (there_is_initialW A) as [n P].
    destruct (can_find_next_position (fun s => s = inr initialW) (fun s => decision (s = inr initialW)) (le_0_n n) P) as [v_end [Q1 [Q2 Q3]]].
    
    exists v_end. destruct A as [V [I F]]. repeat split.
    - unfold initial in I. simpl in I. unfold  vw_state_initial in I. decide (v_end = 0).
      + exfalso. subst v_end. rewrite Q2 in I. discriminate I.
      + omega.
    - assumption.
    - intros k. induction k; intros L.
      + exists initialV. apply I.
      + specialize (V k).
        destruct IHk as [s E]. omega.
        rewrite E in V. simpl in V. destruct (r (S k)) as [s' | s'] eqn:E'.
        * exists s'. reflexivity.
        * exfalso. destruct V as [_ V]. subst s'.
          apply (Q3 (S k)); oauto.
    - intros k. intros L. induction L.
      + now exists initialW.
      + destruct IHL as [s E].
        specialize (V m). rewrite E in V. simpl in V.
        destruct (r (S m)) as[s'|s'] eqn:E'.
        * contradiction V.
        * now exists s'.
  Qed.
      

  Lemma vw_aut_is_vw_omega: L_B vw_aut <$= L_S autV o L_B autW.
  Proof.
    intros w [r A].
    destruct (switch_from_V_to_W A) as [v_end [G0 [kI [OV OW]]]].
    exists (pred v_end). 
    split.
    -  destruct A as [V [I F]]. exists (fun n => if (decision (n >= v_end)) 
                then finalV 
                else match r n with
                   | inl s => s
                   | inr _ => initialV end ).
      repeat split.
      + intros k L. simpl in L.
        rewrite decision_false by omega.
        decide (S k >= v_end); simpl.
        * specialize (V k). destruct (r k) eqn:H.
          -- simpl in V. rewrite_eq (S k = v_end) in V. now rewrite kI in V.
          -- exfalso. specialize (OV k). rewrite H in OV.
             destruct OV as [s E]. omega. discriminate E.
        * destruct (r k) eqn:Ek.
          -- destruct (r (S k)) eqn:ESk.
             ++ specialize (V k). rewrite Ek, ESk in V. now simpl in V.
             ++ exfalso. specialize (OV (S k)). rewrite ESk in OV. destruct OV as [s E]. omega. discriminate.
          -- exfalso. specialize (OV k). rewrite Ek in OV. destruct OV as [s E]. omega. discriminate. 
      + unfold sinitial. rewrite decision_false by omega.
        unfold initial in I. simpl in I. unfold  vw_state_initial in I. rewrite I. apply normV.
      + unfold sfinal. simpl. rewrite decision_true by omega. apply normV.
    - rewrite_eq (S (pred v_end) = v_end).
      exists (fun n => match (drop v_end r) n with |inl _ => initialW |inr s => s end).
      repeat split.
      + intros k. repeat rewrite drop_correct.
        destruct (OW (v_end + k)) as [sk Ek]. omega.
        destruct (OW (v_end + S k)) as [sSk ESk]. omega.
        rewrite Ek, ESk. destruct A as [V [I F]].
        specialize (V (v_end + k)). rewrite_eq (S (v_end + k) = v_end + S k) in V.
        now rewrite Ek, ESk in V.
      + unfold initial. rewrite drop_correct. rewrite_eq (v_end + 0 = v_end).
        rewrite kI. apply normW.
      + exists initialW.
        split.
        * intros n. destruct (initialW_always_final A (n + v_end)) as[m [P Q]].
          exists (m - v_end). split.
          -- omega.
          -- rewrite drop_correct. rewrite_eq (v_end + (m - v_end) = m).
             now rewrite Q.
        * apply normW.
  Qed.     

  Lemma vw_aut_accepts_vw_omega: L_S autV o L_B autW <$= L_B vw_aut.
  Proof.
   intros w [n [[rv [Vv [Iv Fv]]] [rw [Vw [Iw Fw]]]]].
   exists ( (mkstring (seq_map (inl (B:= state autW)) rv) n) +++ (seq_map inr rw)).
   repeat split.
   - simpl. intros k. decide (k <= n).
     + rewrite prepend_path_begin_correct by omega.
       decide (S k <= n) as [D|D].
       * rewrite prepend_path_begin_correct by omega. simpl. split.
         -- apply Vv. simpl. omega.
         -- specialize (Vv  (S k) D). simpl in Vv.
            decide (rv (S k) = finalV) as [D'|D'].
            ++ exfalso. destruct normV as [_ [_ [_ N]]].
               apply (N (w (S k)) (rv (S (S k)))). now rewrite <-D'.
            ++ assumption.
       * rewrite_eq (S k = S n + 0). rewrite prepend_path_rest_correct. simpl. split.
         -- rewrite_eq (k = n). unfold sfinal in Fv. simpl in Fv. apply normV in Fv. rewrite <-Fv.
            apply Vv. simpl. omega.
         -- unfold initial in Iw. now apply normW in Iw.
     + rewrite_eq (S k = S n + (k - n)).
       rewrite_eq (k = S n + (k - S n)).
       repeat rewrite prepend_path_rest_correct.
       rewrite_eq (S n + (k - S n) - n = S (k - S n)).
       specialize (Vw  (k - S n)). rewrite drop_correct in Vw.
       rewrite_eq (S n + (k - S n) = k) in Vw.
       now rewrite_eq (S n + (k - S n)  = k).
   - unfold initial, seq_map. simpl. rewrite prepend_path_begin_correct by omega.
     unfold vw_state_initial. f_equal. now apply normV in Iv.
   - apply final_prepend. exists (inr initialW).
     destruct Fw as [s [Inf Fin]]. apply normW in Fin. subst s. split.
     + intros k. destruct (Inf k) as [m [P W]]. exists m; split; auto.
       unfold seq_map. now f_equal.
     + reflexivity. 
  Qed.

  Lemma vw_aut_correct: L_B vw_aut =$= L_S autV o L_B autW.
  Proof.
    split.
    - apply vw_aut_is_vw_omega.
    - apply  vw_aut_accepts_vw_omega.
  Qed.
End PrependFinLanguage_Automata.

Arguments vw_aut  [A] _ _ _  _ _ : rename.

(** This is the important corollary: given two NFAs A1 and A2, we can construct an NFA which accepts
   [L_S(A1) o L_S(A2)^00]. *)
Corollary  sNFA_sNFA_to_omega_Buechi (A: finType) (autV : NFA A) (autW: BuechiAut A): Sigma aut,
          L_B aut =$= L_S autV o (L_S autW)^00.
Proof.
  destruct (normalize_aut autV) as [normAutV [initialV [finalV [EqV normV]]]].
  destruct (normalize_aut autW) as [normAutW [initialW [finalW [EqW normW]]]].
  pose (w_omega := Womega_aut initialW finalW ).
  exists (vw_aut normAutV initialV finalV w_omega initialW ).
  unfold w_omega. split.
  - intros B.
    apply vw_aut_correct in B; auto.
    + destruct B as [n [V W]].
      exists n. split.
      * now apply EqV.
      * apply w_omega_aut_correct in W; auto. 
        destruct W as [f [Z [Inc W]]].
        exists f. repeat split; auto.
        intros k. apply EqW. apply W.
    + apply w_omega_one_initial_state.
  - intros S.
    apply vw_aut_correct; auto.
    + apply  w_omega_one_initial_state.
    + destruct S as [n [V W]]. exists n. split.
      * now apply EqV.
      * apply  w_omega_aut_correct; auto.
        destruct W as [f [Z [Inc W]]].
        exists f. repeat split; auto. 
        intros k. apply EqW. apply W.
Qed.


















