 Set Implicit Arguments.

Require Import Coq.Init.Nat.
Require Import Coq.Relations.Relation_Definitions.
Require Import BA.External.

Require Import Seqs.
Require Import BA.FinTypes.
Require Import BasicDefs.
Require Import StrictlyMonotoneSeqs.
Require Import SeqOperations.
Require Import NFAs.
Require Import Buechi.
Require Import NFAConstructions.
Require Import Utils.

Hint Resolve transition_dec.
Hint Resolve final_state_dec.
Hint Resolve initial_state_dec.
Hint Resolve finType_exists_dec.

Open Scope string_scope.

Section ConvertToNFA.

  
  Hint Resolve finType_exists_dec.

   Require BA.Automata.

   Context {A:finType}.
   Variable (aut : NFA A).

   Fixpoint seqToList (w : Seq A) k := match k with
      | 0 => cons (w 0) nil
      | S k => cons (w 0) (seqToList (drop 1 w) k)
   end.
   

   Definition stringToList (w: String A) := seqToList w (|w|).

   Lemma seqToListCorrect w k : forall n, n <=k -> nth_error (seqToList w k) n = Some (w n).
   Proof. revert w.
     induction k; intros w n L.
     - now rewrite_eq (n = 0).
     - decide (n = S k).
       + subst n. simpl. now rewrite IHk.
       + simpl. destruct n.
         * reflexivity.
         * simpl. rewrite IHk; auto. omega.
   Qed.

   Lemma stringToListCorrect w : forall n, n <= |w| -> nth_error (stringToList w) n = Some (w [n]).
   Proof.
     destruct w. unfold stringToList. simpl. apply seqToListCorrect.
   Qed.

   Lemma stringToList_Size w: stringToList w = stringToList (mkstring w (|w|)).
   Proof.
     destruct w. now simpl.
   Qed.

   Lemma detlaQstar_decrease_step (w:Seq A) (l:nat)
           (B: Automata.nfa A) (qFin: Automata.Q B) :
           Automata.delta_Q_star Automata.q0 (stringToList (mkstring w (S l))) qFin <-> exists s, 
           Automata.delta_Q_star Automata.q0 (stringToList (mkstring w l)) s /\ Automata.delta_Q s (w (S l)) qFin.
   Proof.
     split.
     - remember (Automata.q0) as s. clear Heqs.
       revert s. revert w. induction l; intros w s QS. 
       + simpl in QS. simpl. destruct QS as [q [T [q' [T' E]]]].
         exists q. split.
         *  exists q; auto.
         * now rewrite E.
       + simpl. 
         destruct QS as [q [T QS]]. unfold stringToList in IHl.
         assert ((drop 1 (mkstring w (S (S l)))) = mkstring  (fun n : nat => w (S n)) (S l)) as H. { reflexivity. }
         rewrite H in QS.
         specialize (IHl (fun n : nat => w (S n)) q QS).
         destruct IHl as [q' P].
         exists q'. split.
         * exists q. simpl in T, P. split.
           -- apply T.
           -- apply P.
         *  apply P.
    - remember (Automata.q0) as s. clear Heqs.
      revert s. revert w. induction l; intros w s QS.
      + destruct QS as [q [[q' [P1 P2]] Q]]. simpl. simpl in P1,P2, Q. exists q. split.
        * now rewrite P2. 
        * exists qFin. auto.
      + simpl. destruct QS as [q [[q' [T' QS]] T]].
        exists q'.   split.
        * now simpl in T'.
        * assert ((drop 1 (mkstring w (S l))) = mkstring  (fun n : nat => w (S n)) (l)) as H. { reflexivity. }
          rewrite H in QS.
          specialize (IHl (mkstring (fun n : nat => w (S n)) l) q').
          apply IHl.
          exists q. split; auto. 
   Qed.


   Lemma detlaQstar_convert(w:String A)
           (B: Automata.nfa A) (qFin: Automata.Q B) :
           Automata.delta_Q_star Automata.q0 (stringToList w) qFin -> exists (r: Seq (Automata.Q B)),
              r 0 = Automata.q0 /\ r (S (|w|)) = qFin /\ forall n, n <= |w| ->  Automata.delta_Q (r n) (w[n]) (r (S n)).
   Proof.
     revert qFin.
     destruct w as [w l].
     induction l ; intros qFin QS.
     - exists  (fun n => match n with |0 => Automata.q0 | _ => qFin end). repeat split; auto.
       simpl. intros n L. rewrite_eq (n = 0).
       simpl in QS. destruct QS as [q' [R F]].
       now rewrite F. 
     - apply detlaQstar_decrease_step in QS.
       destruct QS as [s [QS Q]].
       specialize (IHl s QS).
       destruct IHl as [r [P0 [P1 P2]]].
       exists (fun n => if (decision (n = S (S l))) then qFin else   r n). repeat split.
       + now rewrite decision_false by omega.  
       + simpl. now rewrite decision_true by reflexivity.
       + simpl. intros n L. simpl in P1.
         decide (n =  (S l)) as [D|D].
         * rewrite decision_false by omega.
           rewrite decision_true by omega. rewrite D. now rewrite P1.
         * repeat rewrite decision_false by omega.
           apply P2. simpl. omega.
   Qed.

   Lemma detlaQstar_convert_inverse(w:String A) (B: Automata.nfa A) (qFin: Automata.Q B) :
           (exists (r: Seq (Automata.Q B)),
              r 0 = Automata.q0 /\ r (S (|w|)) = qFin /\ forall n, n <= |w| ->  Automata.delta_Q (r n) (w[n]) (r (S n))) ->
           
           Automata.delta_Q_star Automata.q0 (stringToList w) qFin .
   Proof. 
    intros [r [Be [E T]]].
     enough (forall n, n <= (|w|) -> Automata.delta_Q_star Automata.q0 (stringToList (mkstring (seq w) n )) (r (S n))) as H. {
       rewrite <-E. specialize (H ( (|w|))). simpl in H. 
       unfold drop_string_end in H.  rewrite <-stringToList_Size in H.
       apply H. omega.
    } 
    intros n. induction n; intros L.
     - simpl. exists (r 1 ). split. 
         * simpl in E. rewrite <-Be. apply T. omega.
         * trivial.
     - apply detlaQstar_decrease_step. exists (r (S n)). split.
       + apply IHn. omega.
       + now apply T.
  
   Qed.
   
   Lemma convertoToNFA: Sigma (B : Automata.nfa A), forall w, Automata.n_accept B ( stringToList w) <-> (L_S aut w).
   Proof.
     destruct (normalize_aut aut) as [norm_aut [q0 [f0 [LEQ [[Pq0 [P2q0 _]] _ ]]]]].
     assert (forall s a, forall s', dec (transition (aut:=norm_aut) s a s')) as decDeltaQ. { intros *. auto. }
     assert (forall (s:state norm_aut), dec (final_state s)) as decQacc. { intros. auto. }
   
     exists (Automata.NFA  q0 (DecPred (fun (s:state norm_aut) => final_state s )) (fun s a => DecPred  (fun s' => transition (aut:=norm_aut) s a s'))).
     intros w. split.
     - intros [qFin [Pacc Preach]]. apply LEQ.
       apply detlaQstar_convert in Preach.
       destruct Preach as [r [B [E T]]].
       exists r.
       repeat split. 
       + simpl in T. intros n L. now apply T.
       + unfold sinitial. now rewrite B.
       + unfold sfinal. rewrite E. now simpl in Pacc. 
     - intros L.
       apply LEQ in L.
       destruct L as [r [V [ I F]]].
       exists (r (S(|w|))). split.
       + now simpl.
       + apply detlaQstar_convert_inverse.
         exists r. split.
         * unfold sinitial in I.
           apply P2q0 in I. now rewrite I.
         * split; auto.
   Qed.

   Lemma convertFromNFA (B : Automata.nfa A): (Sigma aut, forall w, (L_S aut w) <-> Automata.n_accept B ( stringToList w)).
   Proof.
      assert (forall (s: Automata.Q B) a (s': Automata.Q B), dec (Automata.delta_Q s a s')) as TransDec by auto.
      assert (forall (s: Automata.Q B), dec (s = Automata.q0)) as InitialDec by auto.
      assert (forall (s: Automata.Q B) , dec(Automata.Q_acc s)) as FinalDec by auto.
      exists (mknfa TransDec InitialDec FinalDec).
      intros w. split.
      - intros [r [V [I F]]].
        exists (r (S(|w|))). split.
        + now simpl.
        + apply detlaQstar_convert_inverse.
         exists r. split.
         * unfold sinitial in I. now simpl in I.
         * split; auto.
      - intros [qFin [Pacc Preach]].
        apply detlaQstar_convert in Preach.
        destruct Preach as [r [Be [E T]]].
        exists r.
        repeat split. 
        + intros n L. simpl. now apply T.
        + unfold sinitial. now rewrite Be.
        + unfold sfinal. rewrite E. now simpl in Pacc.
   Qed. 

End ConvertToNFA.

Section AllAutomaton.

  Context {alphabet:finType}.

  Definition all_state := finType_unit.
  Definition all_state_final := fun (s: all_state) => True.
  Definition all_state_initial := fun (s :all_state) => True.
  Definition all_transition (s:all_state) (a:alphabet) (s':all_state):= True.

  Lemma all_state_final_dec s: dec (all_state_final s). Proof. unfold all_state_final. auto. Qed.
  Lemma all_state_initial_dec s: dec (all_state_initial s). Proof. unfold all_state_initial. auto. Qed.
  Lemma all_transition_dec s a s': dec (all_transition s a s'). Proof. unfold all_transition. auto. Qed.

  Definition all_aut := mknfa all_transition_dec all_state_initial_dec all_state_final_dec.

  Lemma all_aut_accepts_everything: forall w, L_S all_aut w.
  Proof.
    intros w.
    exists (fun n => tt).
    repeat split.
  Qed.
End AllAutomaton.

Section ClosureProperties.

  Context{A:finType}.
  
  Lemma sclosure_union (aut1 aut2: NFA A) : Sigma aut, language_eq (L_S aut) (language_union (L_S aut1) (L_S aut2)).
  Proof.
    destruct (convertoToNFA aut1) as [N1 E1].
    destruct (convertoToNFA aut2) as [N2 E2].
    pose (UA := (Automata.toNFA (Automata.U (Automata.toDFA N1) (Automata.toDFA N2)))).
    destruct (convertFromNFA UA) as [aut EA].
    exists aut.
    unfold language_union. intros w.
    split.
    - intros FA.
      apply EA in FA.
      unfold UA in FA.
      apply Automata.toNFA_correct in FA.
      apply Automata.U_correct in FA.
      destruct FA as [FA|FA]; apply Automata.toDFA_correct in FA.
      + apply E1 in FA. tauto.
      + apply E2 in FA. tauto.
    - intros [F|F]; apply EA;
      try (apply E1 in F); try (apply E2 in F);
      unfold UA;
      apply Automata.toNFA_correct;
      apply Automata.U_correct.
      + left. now apply Automata.toDFA_correct.
      + right. now apply Automata.toDFA_correct.
  Qed.

  Lemma sclosure_intersection (aut1 aut2: NFA A) : Sigma aut, language_eq (L_S aut) (language_intersection (L_S aut1) (L_S aut2)).
  Proof.
    destruct (convertoToNFA aut1) as [N1 E1].
    destruct (convertoToNFA aut2) as [N2 E2].
    pose (IA := (Automata.toNFA (Automata.intersect (Automata.toDFA N1) (Automata.toDFA N2)))).
    destruct (convertFromNFA IA) as [aut EA].
    exists aut.
    unfold language_intersection. intros w.
    split.
    - intros FA.
      apply EA in FA.
      unfold IA in FA.
      apply Automata.toNFA_correct in FA.
      apply Automata.intersect_correct in FA.
      destruct FA as [FA1 FA2]; apply Automata.toDFA_correct in FA1; apply Automata.toDFA_correct in FA2.
      apply E1 in FA1. apply E2 in FA2. tauto.
    - intros [F1 F2]. apply EA.
      apply E1 in F1; apply E2 in F2.
      unfold IA.
      apply Automata.toNFA_correct.
      apply Automata.intersect_correct. split; now apply Automata.toDFA_correct.
  Qed.

  Lemma sclosure_diff (aut1 aut2 : NFA A) : Sigma aut, language_eq (L_S aut) (language_difference (L_S aut1) (L_S aut2)).
  Proof.
    destruct (convertoToNFA aut1) as [N1 E1].
    destruct (convertoToNFA aut2) as [N2 E2].
    pose (UA := (Automata.toNFA (Automata.diff (Automata.toDFA N1) (Automata.toDFA N2)))).
    destruct (convertFromNFA UA) as [aut EA].
    exists aut.
    unfold language_difference. intros w.
    split.
    - intros FA.
      apply EA in FA.
      unfold UA in FA.
      apply Automata.toNFA_correct in FA.
      apply Automata.diff_correct in FA.
      destruct FA as [FA1 FA2].
      split.
      + apply Automata.toDFA_correct in FA1.
        now apply E1.
      + intros A2.
        apply FA2.
        apply Automata.toDFA_correct.
        now apply <-E2.
    - intros [F1 F2].
      apply EA.
      unfold UA.
      apply Automata.toNFA_correct.
      apply Automata.diff_correct.
      split.
      + apply Automata.toDFA_correct. now apply E1.
      + intros A2. apply F2.
        apply Automata.toDFA_correct in A2.
        now apply E2.
  Qed.

  Lemma sclosure_complement (aut : NFA A) : Sigma aut', language_eq(L_S aut') (language_complement (L_S aut)).
  Proof.
    destruct (  sclosure_diff all_aut aut) as [aut' EA].
    exists aut'.
    intros w. unfold language_complement. split.
    - intros F.
      apply EA in F.
      unfold language_difference in F. tauto.
    - intros nF.
      apply EA.
      split.
      + apply all_aut_accepts_everything.
      + assumption.
  Qed.

  Definition sunion (aut1 aut2: NFA A) := match (sclosure_union aut1 aut2) with existT _ aut _ => aut end.
  Definition sdiff (aut1 aut2: NFA A) := match (sclosure_diff aut1 aut2) with existT _ aut _ => aut end.
  Definition scomplement (aut: NFA A) := match (sclosure_complement aut) with existT _ aut' _ => aut' end.
  Definition sintersect  (aut1 aut2: NFA A) := match (sclosure_intersection aut1 aut2) with existT _ aut _ => aut end.


  Lemma sdiff_correct aut1 aut2 : language_eq (L_S (sdiff aut1 aut2)) (language_difference (L_S aut1) (L_S aut2)).
  Proof.
    unfold sdiff.
    now destruct sclosure_diff.
  Qed.

  Lemma scomplement_correct aut: language_eq (L_S (scomplement aut)) (language_complement (L_S aut)).
  Proof.
    unfold scomplement.
    now destruct sclosure_complement.
  Qed.

  Lemma sunion_correct aut1 aut2 : language_eq (L_S(sunion aut1 aut2)) (language_union (L_S aut1) (L_S aut2)).
  Proof.
    unfold sunion.
    now destruct sclosure_union.
  Qed.

  Lemma sintersect_correct aut1 aut2: language_eq (L_S (sintersect aut1 aut2)) (language_intersection (L_S aut1) (L_S aut2)).
  Proof.
    unfold sintersect.
    now destruct sclosure_intersection.
  Qed.

End ClosureProperties.


Lemma many_aut_intersection (A:finType) (l:list (NFA A)) a w:
             L_S (fold_right sintersect all_aut l) w ->  (a el l) ->  L_S a w.
Proof.
  intros L E.
  induction l.
  - contradiction E.
  - destruct E as [E|E].
    + rewrite E in L. simpl in L.
      apply sintersect_correct in L.
      now unfold language_intersection in L.
    + apply IHl.
      * simpl in L. apply sintersect_correct in L.
        now unfold language_intersection in L.
      * assumption.
Qed.
