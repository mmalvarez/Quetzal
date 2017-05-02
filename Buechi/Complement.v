Set Implicit Arguments.

Require Import Coq.Init.Nat.
Require Import Coq.Relations.Relation_Definitions.
Require Import BA.External.
Require Import BA.FinTypes.
Require Import BasicDefs.
Require Import Seqs.
Require Import StrictlyMonotoneSeqs.
Require Import SeqOperations.
Require Import NFAs.
Require Import Buechi.
Require Import NFAConstructions.
Require Import Utils.
Require Import DecLanguageEmpty.
Require Import fin_languages.


Arguments reflexive [A] _ .
Arguments transitive [A] _ .
Arguments symmetric [A] _.
Arguments equiv [A] _.

Close Scope list_scope.
Open Scope string_scope.

(** * Complementation of Buechi Languages *)

(** ** Equivalence Relation on Strings *)

Section TildeEquivalenceRelation.
  
  Context {A:finType}.
  Context {aut:BuechiAut A}.

  Definition transforms (w :String A) (s s': state aut)  :=
      exists r, path r w s s'.

  Definition transforms_final (w:String A) (s s': state aut) :=
      exists r, path r w s s' /\ exists n, n <= S (|w|) /\ final_state (r n).

  Notation " s1 '===>' s2 'on' w" := (transforms w s1 s2) (at level 10).
  Notation " s1 '=!=>' s2 'on' w" := (transforms_final w s1 s2) (at level 10).

  (** *** Facts about [===>] and [=!=>] for Concattenation *)

  Lemma final_transform_implies_transform  s s' w: s =!=> s' on w -> s ===> s' on w.
  Proof.
    intros [r [P _]]. now exists r.
  Qed.
 
  Lemma split_transforms u w s s': s ===> s' on (u ++ w) -> exists s'', s ===> s'' on u /\ s'' ===> s' on w.
  Proof.
    intros [r W].
    destruct (split_path W) as [s'' [P1 P2]].
    exists s''. split.
    - now exists r.
    - now exists ((drop (S (| u |)) r)).
  Qed.

  Lemma combine_transforms u v s s' s'' : s ===> s'' on u -> s'' ===> s' on v -> s ===> s' on (u++v).
  Proof.
    intros [r1 W1] [r2 W2].
    exists (prepend_path (|u|) r1 r2).
    now apply (concat_paths (aut:=aut) (s'':=s'')).
  Qed.

  Lemma split_final_transforms u w s s': s =!=> s' on (u ++ w) -> exists s'',
         (s =!=> s'' on u /\ s'' ===> s' on w) \/ (s ===> s'' on u /\ s'' =!=> s' on w).
  Proof.
    intros [r [V [n [L F]]]].
    destruct (split_path V) as [s'' [P1 P2]].
    exists s''.
    decide (n <= S(|u|)) as [D|D].
    - left. split.
      + exists r. split; firstorder.
      + now exists (drop (S (| u |)) r) .
    - right. split.
      + now exists r.
      + exists (drop (S (| u |)) r). split; auto.
        exists (n - (S(|u|))). split.
        * simpl in L.  omega.
        * rewrite drop_correct. now rewrite_eq (S(|u|) + (n - S(|u|)) = n).
  Qed.

  Lemma combine_final_transforms_left u w s s' s'' : s =!=> s'' on u -> s'' ===> s' on w  -> s =!=> s' on (u++w).
  Proof.
    intros [r1 [W1 [n1 [L1 F1]]]] [r2 W2].
    exists (prepend_path (|u|) r1 r2). split.
    - now apply (concat_paths (aut:=aut)) with (s'':=s'').
    - exists n1. split.
      + simpl. omega.
      + decide (n1 <= |u|) as [D|D].
        * now rewrite prepend_path_begin_correct.
        * rewrite prepend_path_rest_correct2 with (n:=0).
          -- rewrite <-(adjacent_paths_agree W1 W2). now rewrite_eq (S (|u|) = n1).
          -- omega.
  Qed.

  Lemma combine_final_transforms_right u w s s' s'' : s ===> s'' on u -> s'' =!=> s' on w  -> s =!=> s' on (u++w).
  Proof.
    intros [r1 W1] [r2 [W2 [n2 [L2 F2]]]].
    exists (prepend_path (|u|) r1 r2). split.
    - now apply (concat_paths (aut:=aut)) with (s'':=s'').
    - exists (n2 + S(|u|)). split.
      + simpl. omega.
      + rewrite prepend_path_rest_correct2 with (n:=n2); oauto.
  Qed.

  (** *** Definition of the Equivalence Relation [~~] *)

  Definition tilde_equiv (w v : String A) := forall s s',
      (s ===> s' on w <-> s ===> s' on v) /\
      (s =!=> s' on w <-> s =!=> s' on v).

  Notation "w ~~ v" := (tilde_equiv w v) (at level 60).

  Lemma tilde_reflexive : reflexive tilde_equiv.
  Proof.
    intros w. split; tauto.
  Qed.

  Lemma tilde_transitive : transitive tilde_equiv.
  Proof.
    intros u v w UV VW.
    repeat split; 
       destruct (UV s s') as [[uTv vTu] [uFv vFu]];
       destruct (VW s s') as [[vTw wTv] [vFw wFv]];
       tauto.
  Qed.

  Lemma tilde_symmetric : symmetric tilde_equiv.
  Proof.
    intros w v WV.
    repeat split; destruct (WV s s') as [[uTv vTu] [uFv vFu]]; tauto.
  Qed.

  Lemma tilde_equivalence : equiv tilde_equiv.
  Proof.
     unfold equiv. auto using tilde_reflexive, tilde_transitive, tilde_symmetric.
  Qed.

  (** [~~] is a congruence relation *)

  Definition congruence (R : String A -> String A -> Prop) := forall (u v w : String A), R u v -> R (u ++ w) (v ++ w).
  
  Hint Unfold tilde_equiv.

  Lemma tilde_congruence : congruence tilde_equiv.
  Proof.
    intros u v w UV.
    split.
    - split; intros T; destruct (split_transforms T) as [s'' [P1 P2]];
       apply (combine_transforms) with (s'':=s''); destruct (UV s s'') as [[? ?][? ?]]; auto.
    - split; intros T; destruct (split_final_transforms T) as [s'' [[F1 P2]|[P1 F2]]]; 
      [ apply combine_final_transforms_left with (s'':=s'') |
        apply combine_final_transforms_right with (s'':=s'')|
        apply combine_final_transforms_left with (s'':=s'') |
        apply combine_final_transforms_right with (s'':=s'') ]; 
       destruct (UV s s'') as [[? ?] [? ?]]; auto.
  Qed.

  (** Extensionality of [~~] *)

  Lemma transforms_extensional w w' s s': s ===> s' on w -> w == w' -> s ===> s' on w'.
  Proof.
    intros [r P] EW.
    exists r. now apply (path_extensional  (w:=w)).
  Qed.

  Lemma final_transforms_extensional w w' s s': s =!=> s' on w ->  w == w' -> s =!=> s' on w'.
  Proof.
    intros [r [P [n Q]]] EW.
    exists r. split.
    - now apply (path_extensional  (w:=w)).
    - exists n. split.
      + destruct EW as [EL _]. now rewrite <-EL.  
      + tauto.
  Qed. 

  Lemma tilde_extensional w v w' v': w ~~ v -> w == w' -> v == v' -> w' ~~ v'.
  Proof.
    intros WV EW EV.
    pose (EW' := string_equal_symmetric EW); pose (EV' := string_equal_symmetric EV). 
    unfold tilde_equiv.
    intros s s'. repeat split; intros T.
    - apply (transforms_extensional (w:=v)); auto. apply WV.
      now apply (transforms_extensional (w:=w')).
    - apply (transforms_extensional (w:=w)); auto. apply WV.
      now apply (transforms_extensional (w:=v')).
    - apply (final_transforms_extensional (w:=v)); auto. apply WV.
      now apply (final_transforms_extensional (w:=w')).
    - apply (final_transforms_extensional (w:=w)); auto. apply WV.
      now apply (final_transforms_extensional (w:=v')).
  Qed.

  (** Decidability of [~~] *)

  Lemma bound_path_unchanged r w (s s':state aut): path r w s s' -> path (to_seq (to_bounded (m:=S (|w|))  r)) w s s'.
  Proof.
    intros [V [B E]]. repeat split.
    - apply bounded_run_is_valid_path; oauto.
    - rewrite bounded_unchanged; oauto.
    - rewrite bounded_unchanged; oauto.
  Qed.

  Instance dec_transforms : forall s s' w, dec (s ===> s' on w).
  Proof.
    intros s s' w. unfold transforms.
    enough (dec (exists r : (state aut) ^ (finType_Le_K (S (|w|))), path (to_seq r) w s s')) as H.
    - destruct H as [H|H].
      + left. destruct H as [r H]. now exists (to_seq r).
      + right. intros [r E]. apply H. exists (to_bounded r).
        now apply bound_path_unchanged.
    - auto.
  Defined.

  Lemma there_is_final_index (w:String A) (r: (state aut) ^ (finType_Le_K (S (|w|)))) (L : Le_K (S (| w |))): 
              final_state (applyVect r L) -> exists n,  n <= S (| w |) /\ final_state (to_seq r n).
  Proof.
    intros V.
    destruct L as [n L'] eqn:E.
    assert (n <= S(|w|)) as L''. { change (le_k (S (|w|)) n). rewrite pure_equiv. apply L'. }
    exists n. split;auto.
    rewrite <-E in V.
    rewrite (to_seq_unchanged  r L'' ).
    assert(create_Le_K L'' = L) as H. { rewrite E. unfold create_Le_K. f_equal. apply pure_eq. }
    now rewrite H.
  Qed.

  Instance dec_transforms_final : forall s s' w, dec(s =!=> s' on w).
  Proof.
  intros s s' w. unfold transforms_final.
    enough (dec (exists r : (state aut) ^ (finType_Le_K (S (|w|))), path (to_seq r) w s s' /\
     (exists  L: Le_K (S (| w |)), final_state (applyVect r L)))) as H.
    - destruct H as [H|H].
      + left. destruct H as [r [H1 [L H2]]].  exists (to_seq r). split; auto.
        apply (there_is_final_index H2).
      + right. intros [r [E1 [n [L E2]]]]. apply H. exists (to_bounded r). split.
        * now apply bound_path_unchanged.
        * exists (create_Le_K L). now rewrite (to_bounded_unchanged). 
    - auto.
  Defined.

  (** Given [===>] or [=!=>] we can compute the run on the NFA *)

  Lemma finType_cc_sigma (X: finType) (p: X -> Prop) (dec_p: forall x, dec (p x)): (exists x, p x) -> (Sigma x, p x).
  Proof.
    intros E.
    destruct (finType_cc dec_p E) as [x px].
    exists x; auto.
  Qed.

  Arguments finType_cc [X] [p] [D] _.

  Lemma compute_run_transforms s s' w :  s ===> s' on w -> Sigma r, path r w s s'.
  Proof.
    intros T.
    enough (Sigma (r: (state aut) ^ (finType_Le_K (S (|w|)))), path (to_seq r) w s s').
    - destruct X as [r P]. now exists (to_seq r).
    - apply finType_cc_sigma.
      + auto.
      + destruct T as [r P]. exists (to_bounded r).
        now apply bound_path_unchanged.
  Qed.

  (* Need the products instead of conjunctions in this lemma because we will destruct it in functions later *)
  Lemma compute_run_final_transforms s s' w : s =!=> s' on w -> Sigma r, prod (path r w s s') (Sigma n, prod (n <= S (|w|)) (final_state (r n))).
  Proof.
    intros T.
    enough (Sigma (r: (state aut) ^ (finType_Le_K (S (|w|)))), prod (path (to_seq r) w s s')((Sigma (L : Le_K (S (| w |))), final_state (applyVect r L)))).
    - destruct X as [r [P1 [L P2]]]. destruct L as [n L'] eqn:E.
      exists (to_seq r). split;auto.
      assert (n <= S(|w|)) as L'' by (rewrite pure_equiv; apply L'). 
      exists n. split; auto.
      rewrite <-E in P2.  rewrite (to_seq_unchanged  r L'').
      assert(create_Le_K L'' = L) as H. { rewrite E. unfold create_Le_K. f_equal. apply pure_eq. }
      now rewrite H.
    - enough (exists (r: (state aut) ^ (finType_Le_K (S (|w|)))),  (path (to_seq r) w s s') /\ (exists (L : Le_K (S (| w |))), final_state (applyVect r L))).
      + destruct (finType_cc  H) as [r [P1 P2]].
        exists r. split; auto.
        destruct (finType_cc P2) as [L P3]. now exists L. 
      + destruct T as [r [P1 [n [P2 P3]]]].
        exists (to_bounded r). split.
        * now apply bound_path_unchanged.
        * exists (create_Le_K P2).
          now rewrite to_bounded_unchanged.
  Qed.

  (** *** Finite Type for Equivalence Classes of [~~] *)
  
  Definition EquivalenceClassIndex := (? finType_bool) ^ (state aut (x) state aut).
  Definition TildeEquivalenceClass (i :  EquivalenceClassIndex) : StringLang A := fun w =>
            forall s, forall s', match (applyVect i (s,s')) with
               | None => ~ (s ===> s' on w)
               | Some false => (s ===> s' on w) /\ ~(s =!=> s' on w)
               | Some true => s =!=> s' on w
              end.
  
  Notation "{[ i ]}" := (TildeEquivalenceClass i) (at level 0).
  
  Definition tilde_eq_class w : EquivalenceClassIndex:= (vectorise (fun z => match z with 
                (s,s') => if (decision (s ===> s' on w))
                            then if (decision (s =!=> s' on w))
                                then Some true
                                else Some false
                            else None end)).

  Lemma tilde_eq_class_correct w: {[tilde_eq_class w]} w.
  Proof.
    unfold tilde_eq_class. intros s s'. 
    rewrite apply_vectorise_inverse.
    decide (s ===> s' on w) as [D|D].
    - decide (s =!=> s' on w) as [D2|D2]; auto.
    - auto.
  Qed.

  Lemma equivalence_class_closed i u w: {[i]} w -> u ~~ w -> {[i]} u.
  Proof.
    intros WI UW s s'.
    specialize (WI s s').
    destruct (applyVect i (s,s')) as [[|]|] .
    - now apply UW.
    - split.
      + now apply UW.
      + intros NU. apply WI. now apply UW.
    - intros NU. apply WI. now apply UW.
  Qed.

  Lemma equivalent_in_equivalence_class i w w': {[i]} w -> {[i]} w' -> w ~~ w'.
  Proof.
    intros WI W'I s s'.
    specialize (WI s s'). specialize (W'I s s').
    destruct (applyVect i (s,s')) as [[|]|].
    - repeat split; auto using final_transform_implies_transform.
    - destruct WI;destruct W'I. repeat split; intros L; auto ; try (exfalso ;auto).
    - repeat split; intros L; exfalso; auto using final_transform_implies_transform .
  Qed.

  Lemma equivalent_if_same_equivalence_class w w': tilde_eq_class w = tilde_eq_class w' -> w ~~ w'.
  Proof.
    intros E.
    apply (equivalent_in_equivalence_class (i := tilde_eq_class w)).
    - apply tilde_eq_class_correct.
    - rewrite E. apply tilde_eq_class_correct.
  Qed.  

  Lemma equivalent_drop n m k j v: k <= n < m ->
           {[j]} (extract n m v)   ->
           {[j]} (extract (n - k) (m - k) (drop k v)) .
  Proof.
    intros L E.
    apply (equivalence_class_closed E).
    apply (tilde_extensional (w:=(extract n m v)) (v:=(extract n m v))).
    - apply tilde_reflexive.
    - split.
      + simpl. omega.
      + intros i iL. simpl.
        repeat rewrite drop_correct. f_equal. omega.
    - apply string_equal_reflexive. 
  Qed.

  Lemma tilde_eq_class_congruence v w u: tilde_eq_class w = tilde_eq_class v -> tilde_eq_class (w ++ u) = tilde_eq_class (v ++ u).
  Proof.
    intros E.
    pose (Q := equivalent_if_same_equivalence_class E).
    pose (C:=tilde_congruence u Q).

    apply vector_extensionality.
    unfold tilde_eq_class. simpl. unfold getImage. apply list_eq.
    induction (elem (state aut (x) state aut)); intros n.
    - reflexivity.
    - simpl. destruct n; simpl. 
      + destruct a as [s s']. decide (s ===> s' on (w ++ u)) as [D|D].
        * decide (s =!=> s' on (w ++ u)) as [D'|D'].
          -- repeat rewrite decision_true; auto; now apply C.
          -- rewrite decision_true. rewrite decision_false; auto.
             ++ intros T. apply C in T. tauto.
             ++ now apply C.
        * rewrite decision_false. reflexivity.
          intros T. apply C in T. tauto.
      + apply IHl.
  Qed. 

  Instance dec_tilde_eq_class i w: dec( {[i]} w).
  Proof.
    unfold TildeEquivalenceClass.
    apply finType_forall_dec. intros s.
    apply finType_forall_dec. intros s'.
    destruct (applyVect i (s,s')) as [[|]|]; auto.
  Defined. 

  (** **** Equivalence classes can be recognized by NFAs 
      There aretwo ways to show this: using Myhill Nerode or Closure Properties of NFAs*)

  Section TildeEquivalenceClassRecognizableMyhillNerode.

    (** Myhill-Nerode is only proven for Strings including the empty String. We do not prove it here.
        Quickly define EStrings (String including the empty one) and the EString language of an NFA *)

    Definition EString := option (String A).

    Definition econcat (s1 s2: EString) := match s1,s2 with
       | None, None => None
       | None, Some _ => s2
       | Some _ , None => s1
       | Some s1, Some s2 => Some (s1 ++ s2) end.

    Definition seaccepting (aut: NFA A) r s := match s with 
      | None => initial_state (r 0) /\ final_state (aut:=aut) (r 0)
      | Some w => saccepting r w
    end.

    Definition selanguage (aut:NFA A) := fun w => exists r, seaccepting (aut:=aut) r w.

    (** Myhill-Nerode Theorem, without proof *)

    Definition right_congruent (X: Type) (f: EString -> X) := forall x y, f x = f y -> forall a, f (econcat x a) = f (econcat y a).
    Definition classifier (X: finType) (f: EString -> X) := right_congruent f.
    Definition refines (X: finType) (f:EString ->X) (L: Language EString) := forall x y, f x = f y -> (L x <-> L y).

    Definition MyhillNerode (X:finType) (f: EString -> X) (L: Language EString) :=
      (forall s, dec (L s)) -> classifier f -> refines f L ->  { aut| selanguage aut =$= L}.

    Lemma equalSELangImpliesEqualSLang (a: NFA A) (L: StringLang A) (P:Prop): selanguage a  =$= (fun (s:EString) => match s with
         | None => P
         | Some w => L w
       end ) -> L_S a =$= L.
    Proof.
      intros E w.
      now specialize (E (Some w)).
    Qed.  

    (** No we obtain the desired NFA to recognize a equivalence class when we use the equivalence classes as classifier. *)

    Lemma tilde_equiv_class_NFA_recognizable_MyhillNerode (i:EquivalenceClassIndex) : (forall X f L, MyhillNerode (X:=X) f L) ->
        Sigma aut, slanguage aut =$= {[i]}.
    Proof.
      intros M.
      pose (f:= fun (s:EString) => match s with 
            | None => None
            | Some w => Some (tilde_eq_class w)
           end).
      pose (L:= fun(s:EString) => match s with 
            | None => False
            | Some w => {[i]} w
           end).
      assert (forall s, dec (L s)) as decL. { intros s. unfold L. destruct s; auto. }
      assert (classifier f) as clasF. { unfold f. intros x y E a. destruct x,y,a ;simpl; try discriminate; auto.
         f_equal. apply tilde_eq_class_congruence. congruence. }
      assert (refines f L) as ref. { unfold f, L. intros x y E. destruct x as [w|]; destruct y as [v|]; try discriminate.
         - split.
           + intros W. apply (equivalence_class_closed W). apply equivalent_if_same_equivalence_class. congruence.
           + intros V. apply (equivalence_class_closed V). apply equivalent_if_same_equivalence_class. congruence.
         - tauto. }
      destruct (M (? EquivalenceClassIndex) f L decL clasF ref) as [a P].
      exists a.
      unfold f, L in *.
      now apply (equalSELangImpliesEqualSLang (P:=False)).
    Qed.

  End TildeEquivalenceClassRecognizableMyhillNerode.

  (** This Section is not as nice, but it is not as intersting. If I would use the automata of the
      Doczkal library to have a proof for Myhill Nerode and to apply the section before,
      but because I use the finite types of Jan's bachelor thesis it was right easy to show the equivalence of my NFAs to his
      and to obtain closure properties from them *)

  Section TildeEqivalenceClassRecognizable.

    Hint Resolve final_state_dec.
    Hint Resolve initial_state_dec.
    Hint Resolve transition_dec.
    Hint Resolve finType_exists_dec.

    Section TransformsRecognizable.
      Variable (startS : state aut).
      Variable (endS: state aut).

      Definition tf_state := (state aut).
      Definition tf_state_initial s := s = startS.
      Definition tf_state_final s := s = endS.
      Definition tf_transition s a s' :=  transition (aut:=aut) s a s'.

      Lemma tf_state_initial_dec s : dec(tf_state_initial s). Proof. unfold tf_state_initial. auto. Qed.
      Lemma tf_state_final_dec s : dec(tf_state_final s). Proof. unfold tf_state_final. auto. Qed.
      Lemma tf_transition_dec s a s': dec (tf_transition s a s'). Proof. unfold tf_transition. auto. Qed.
    
      Definition tf_aut := mknfa tf_transition_dec tf_state_initial_dec tf_state_final_dec.

      Lemma tf_accepts_tranforms w: (startS ===> endS on w)-> L_S tf_aut w.
      Proof.
        intros [r [V [B E]]].
        exists r.
        repeat split; auto.
      Qed.

      Lemma tf_is_transforms w: L_S tf_aut w -> (startS ===> endS on w).
      Proof.
        intros [r [V [I F]]].
        exists r. repeat split; auto.
      Qed.

      Lemma tf_recognizes_transforms w : startS ===>endS on w <-> (L_S tf_aut w).
      Proof.
        split. apply tf_accepts_tranforms. apply tf_is_transforms.
      Qed.

    End TransformsRecognizable.

    Section TransformsFinalRecognizable.
      Variable (startS : state aut).
      Variable (endS: state aut).

      Definition tff_state := (state aut) (x) finType_bool.
      Definition tff_state_initial s := s = (startS,false) \/ (s = (startS,true) /\ final_state startS).
      Definition tff_state_final s := s = (endS, true).
      Definition tff_transition s a s' :=  match s,s' with
           | (s, true),(s',true) => transition (aut:=aut) s a s'
           | (s, false), (s', true) => transition (aut:=aut) s a s' /\ final_state s'
           | (s, false), (s', false) => transition (aut:=aut) s a s'
           | _,_ => False
           end.

      Lemma tff_state_initial_dec s : dec(tff_state_initial s). Proof. unfold tff_state_initial.  auto. Qed.
      Lemma tff_state_final_dec s : dec(tff_state_final s). Proof. unfold tff_state_final.  auto. Qed.
      Lemma tff_transition_dec s a s': dec (tff_transition s a s'). Proof. unfold tff_transition. destruct s as [s [|]];destruct s' as[s' [|]]; auto. Qed.
    
      Definition tff_aut := mknfa tff_transition_dec tff_state_initial_dec tff_state_final_dec.

      Lemma tff_accepts_tranforms_final w: (startS =!=> endS on w)-> L_S tff_aut w.
      Proof.
        intros [r [[V [B E]] [k [Lk Fk]]]].
        exists (fun n => if (decision (n < k))
                         then (r n, false)
                         else (r n, true)).
        repeat split.
        - intros n L.
          decide (n < k).
          + decide (S n < k). 
            * now apply V.
            * simpl. split.
              -- now apply V.
              -- now rewrite_eq (S n = k).
          + rewrite decision_false by omega. simpl. now apply V.
        - unfold sinitial.
          decide (0 < k).
          + simpl. rewrite B. unfold tff_state_initial. tauto.
          + simpl. unfold tff_state_initial. rewrite B.
            rewrite_eq (k = 0) in Fk. rewrite B in Fk. tauto.
        - simpl. unfold tff_state_final.
          rewrite decision_false by omega.
          now rewrite E.    
      Qed.

      Lemma tff_is_transforms_final w: L_S tff_aut w -> startS =!=> endS on w.
      Proof.
        intros [r [V [I F]]].
        exists (seq_map fst r).
        repeat split; unfold seq_map.
        - intros n L.
          specialize (V n).
          destruct (r n) as[sn [|]]; destruct (r (S n)) as[ sSn [|]]; simpl; simpl in V; try (now apply V).
          contradiction V.
        - unfold sinitial in I.
          destruct (r 0).
          simpl in I. unfold tff_state_initial in I.
          simpl. destruct I as [I | [I _]]; congruence.
        - unfold sfinal in F.
          destruct (r (S(|w|))).
          simpl. simpl in F. unfold tff_state_final in F.
          congruence.
        - assert (0 <= S(|w|)) as H by omega.
          pose ( p := fun (s:tff_state) => snd s = true).
          assert (p (r (S(|w|)))) as H2. { unfold p. simpl in F. unfold tff_state_final in F. rewrite F. now simpl. }
          assert (forall s, dec (p s)) as decP. { intros s. unfold p. auto. }
          destruct (can_find_next_position decP H H2) as [n [L [P Q]]].
          exists n. split.
          +  omega.
          +  destruct n.
            * unfold p in P.
              destruct I as [I | [I1 I2]].
              -- exfalso. destruct (r 0).
                 simpl in P. rewrite P in I. congruence.
              -- now rewrite I1.
            * specialize (V n).
              unfold p in P. 
              assert (n <= |w|) as Hz by omega.
              specialize (V Hz).
              simpl in V. unfold tff_transition in V.
              destruct (r n) as [rn [|]] eqn:N; destruct (r (S n)) as [rSn [|]] eqn:SN.
              -- exfalso. apply (Q n).
                 ++ omega.
                 ++ now rewrite N.
              -- exfalso. simpl in P. congruence.
              -- now simpl.
              -- exfalso. simpl in P. congruence.
       Qed.  

      Lemma tff_recognizes_transforms_final w: (startS =!=> endS on w) <->  L_S tff_aut w. 
      Proof.
        split. apply tff_accepts_tranforms_final. apply tff_is_transforms_final.
      Qed.
   End TransformsFinalRecognizable.

   Context { V : EquivalenceClassIndex}.

   Definition s_s'_pair_aut (p :(state aut) (x) (state aut)):=
    let (s, s') := p in 
    match (applyVect V (s, s')) with
       | None => scomplement (tf_aut s s')
       | Some false => sdiff (tf_aut s s') (tff_aut s s')
       | Some true => (tff_aut s s')
   end.

   Definition tilde_equiv_class_aut := fold_right
     sintersect all_aut 
     (map s_s'_pair_aut (elem ((state aut) (x) (state aut)))) .

   Lemma tilde_equiv_class_aut_accepts_Equiv_class: {[V]} <$= L_S tilde_equiv_class_aut.
   Proof.
     intros w wV.  unfold TildeEquivalenceClass in wV. unfold tilde_equiv_class_aut.
     induction (elem (state aut (x) state aut)).
     - simpl. apply all_aut_accepts_everything.
     - simpl. apply sintersect_correct. split.
       + unfold s_s'_pair_aut.
         destruct a as [s s'].
         specialize (wV s s').
         destruct (applyVect V (s, s')) as [[|]|] eqn:H.
         * now apply tff_recognizes_transforms_final.
         * apply sdiff_correct. split.
           -- now apply tf_recognizes_transforms.
           -- intros N. apply wV. now apply tff_recognizes_transforms_final.
         * apply scomplement_correct.
           intros T. apply wV.
           now apply tf_recognizes_transforms.  
       + apply IHl.
  Qed.

  Lemma tilde_equiv_class_aut_is_equiv_class: L_S tilde_equiv_class_aut <$= {[V]}.
  Proof.
    intros w wA.
    unfold tilde_equiv_class_aut in wA.
    intros s s'.
    assert (L_S (s_s'_pair_aut (s,s')) w) as H. {
      apply (many_aut_intersection wA).
      apply in_map_iff.
      exists ((s,s')).
      split;auto.
    }
    unfold s_s'_pair_aut in H.
    destruct (applyVect V (s, s')) as [[|]|].
    - now apply tff_recognizes_transforms_final.
    - apply sdiff_correct in H. destruct H as [H1 H2]. split.
      + now apply tf_recognizes_transforms.
      + intros F. apply H2. now apply tff_recognizes_transforms_final.
    - intros F.
      apply scomplement_correct in H.
      apply H.
      now apply tf_recognizes_transforms.
  Qed.

  Lemma tilde_equiv_class_NFA_recognizable: {[V]} =$= L_S tilde_equiv_class_aut.
  Proof.
   intros w. split.
   - apply tilde_equiv_class_aut_accepts_Equiv_class.
   - apply tilde_equiv_class_aut_is_equiv_class.
  Qed.
  
  End TildeEqivalenceClassRecognizable.
  
  Corollary eq_classes_extensional i: StringLang_Extensional {[i]}.
  Proof.
    intros w w' C E.
     (* Could be derived from definiton, but I showed that all [i] are finite
               automaton recognizable and languages are extensional *)
    pose (f := tilde_equiv_class_NFA_recognizable (V:=i)).
    apply f.
    apply (slanguage_extensional (w:=w)); auto.
    now apply f.
  Qed.

  
  (** NFA recognizing [V o W^00]*)
  Definition VW_aut i j := projT1 (sNFA_sNFA_to_omega_Buechi (tilde_equiv_class_aut (V:=i)) (tilde_equiv_class_aut (V:=j))).
    
  Lemma VW_aut_correct i j: L_B (VW_aut i j) =$= {[i]}o{[j]}^00.
  Proof.
    unfold VW_aut.
    destruct (sNFA_sNFA_to_omega_Buechi) as [a P]. simpl.
    intros w; split.
    - intros B. apply P in B. destruct B as [n [Q1 [f [Inc [Z Q2]]]]].
      exists n. split.
      + now apply (tilde_equiv_class_NFA_recognizable (V:= i) (mkstring w n) ). 
      + exists f; repeat split; auto. intros k.
        now apply (tilde_equiv_class_NFA_recognizable (V:= j) (extract (f k) (f (S k)) (drop (S n) w))).
    - intros B. apply P. destruct B as [n [B1 [f [Inc [Z B2]]]]].
      exists n. split.
      + now apply (tilde_equiv_class_NFA_recognizable (V:= i) (mkstring w n)).
      + exists f; repeat split; auto. intros k.
        now apply (tilde_equiv_class_NFA_recognizable (V:= j) (extract (f k) (f (S k)) (drop (S n) w))).
  Qed.
  

  (** ** Compatibility of [V o W ^00] with [L_B aut] *)

  Lemma leq_0 x : 0 <= x.
  Proof. omega. Defined.
 
  Section Compatibility.
    (** Now put a lot on the table: given two sequences [ow] [ow'] and an accepting run for [ow] *)
    Variables (ow ow' : Seq A).
    Variables (r : Run aut).
    Variables (Acc: accepting r ow).

    (** And both strings are pointwise equivalent to some [v +++ (w1 ++ w2 ++ ..)] *)
    Variable (v v' : String A).
    Variable (w w' : Seq (String A)).
    Variable (Eq: (forall n : nat, ow n = (v +++ (concat_inf w)) n)).
    Variable (Eq':(forall n : nat, ow' n = (v' +++ (concat_inf w')) n)).
    
    (** and the v v' resp wi w'i are from the same ~ equivalence class *)
    Variables (i j: EquivalenceClassIndex).
    Variables (V: {[i]} v )(V': {[i]} v').
    Variables (W: (forall n, {[j]} (w n) ))(W': (forall n, {[j]} (w' n))).
    
    (** and r gets partitioned into r0 R according to v w *)
    Variable (r0 : String (state aut)).
    Variable (R : Seq (String (state aut))).
    Variable (EqR: (forall n, r n = (r0 +++ concat_inf R) n)).

    Variable (eqLengthv: (|r0| = |v|)).
    Variable (valid_r0: (valid_path  (seq r0) v)).
    Variable (agree_r0: (r0 [S(|r0|)] = (R 0) [0])).
    Variable (valid_R : (forall k, |R k| = |w k| /\
        valid_path (seq (R k)) (w k))).
    Variable (agree_R: (forall k, (R k)[ S(|R k|)] = (R (S k)) [0])).

    (** Then we can show that there is an accepting run for ow' *)
   
    (* predicate that tells whether in R k is a final state, so wether on w k there is a final state *)
    Definition W_final := fun k => visits_final (R k).
    Definition pure_W_final := pure W_final.

    Lemma W_final_iff k: W_final k <-> pure_W_final k.
    Proof.
      unfold pure_W_final. apply pure_equiv.
    Qed.

    Instance dec_pure_W_final: forall k, dec (pure_W_final k).
    Proof.
      intros k. unfold pure_W_final.
      decide (W_final k) as [D|D].
      - left. now apply pure_equiv.
      - right. intros np.
        apply D. rewrite pure_equiv. apply np.
    Qed.  
         
    Lemma v_transforms: (r0 [0]) ===> (R 0) [0] on v .
    Proof.
      exists (seq r0). 
      rewrite <-agree_r0. split; auto. 
    Qed.

    Lemma W_transforms: forall k,  (R k)[0] ===> (R (S k)) [0] on (w k) /\
                                   (W_final k -> (R k)[0] =!=> (R (S k)) [0] on (w k)).
    Proof.
      intros k. specialize (agree_R k). destruct (valid_R k) as [E P]. split.
      - exists (seq (R k)). split.
        + trivial.
        + now rewrite <-E.  
     - intros F. exists (seq (R k)). repeat split.
        + assumption. 
        + now rewrite <-E.
        + destruct F as [m [L F]]. exists m. split; oauto.
    Qed. 
  
    Lemma v'_transforms: (r0 [0]) ===> (R 0) [0] on v'.
    Proof.
      apply (equivalent_in_equivalence_class V V').
      apply v_transforms.
    Qed.

    Lemma W'_transforms :
      forall k, (R k)[0] ===> (R (S k)) [0] on (w' k) /\
                  (pure_W_final k -> (R k)[0] =!=> (R (S k)) [0] on (w' k)).
    Proof.
      intros k. split.
      - apply (equivalent_in_equivalence_class (W k) (W' k)). apply W_transforms.
      - intros F. rewrite <-W_final_iff in F.
        apply (equivalent_in_equivalence_class (W k) (W' k)). now apply W_transforms.
    Qed.
 
    (** Build the accepting run for [ow'] *)
    (** Runs for the strings in W'. Need to check whether W is final to ensure that the run for W' is final, too *)
    Definition R' : Seq (String (state aut)):= fun k => match (dec_pure_W_final k) with
           | left B => match (W'_transforms k ) with
              | conj _ Z => mkstring (projT1 (compute_run_final_transforms (Z B))) (|w' k|)  end
           | _ => match (W'_transforms k) with
              | conj Z _ => mkstring  (projT1 (compute_run_transforms Z)) (|w' k|) end end.
    (** Run on ow' is obtained from concatting the run on v' to R' *)
    Definition r' : (Run aut):=  (mkstring (projT1 (compute_run_transforms v'_transforms)) (|v'|)) +++ (concat_inf R').

    Ltac destruct_compute_run_maybe_final_transforms := try (destruct compute_run_final_transforms); try (destruct compute_run_transforms).
    Ltac destruct_in_R' := destruct dec_pure_W_final; destruct W'_transforms; destruct_compute_run_maybe_final_transforms.

    Lemma R'k0_eq_Rk0: forall k, (R' k) [0] = (R k) [0].
    Proof.
      intros k. unfold R'.
      destruct_in_R'; simpl; unfold path in *; tauto.
    Qed.

    Lemma valid_r' : valid_run  r' ow'.
    Proof.
      apply (valid_run_extensional (r:=r') (w:=v' +++ concat_inf w')); auto.
      unfold r'. apply prepend_string_is_valid.
        - reflexivity.
        - destruct (compute_run_transforms v'_transforms) as [x P]. simpl. apply P.
        - destruct (compute_run_transforms v'_transforms) as [x P].
          unfold concat_inf. simpl. rewrite R'k0_eq_Rk0. apply P.
        - unfold R'. apply concat_inf_is_valid. intros n. repeat split.
          + now destruct_in_R'.
          + destruct_in_R'; unfold path in *; simpl; tauto.
          + assert (forall x y, x (S (| w' n |)) = (R (S n)) [0] -> y 0 = (R (S n)) [0] -> x (S (| w' n |)) = y 0) as T. {
               intros x y E1 E2. now rewrite E1, E2. }
            repeat destruct_in_R'; simpl; unfold path in *; apply T; tauto.
    Qed.

    Lemma initial_r' : initial r'.
    Proof.
      unfold initial, r'. simpl.
      destruct (compute_run_transforms v'_transforms) as [x [? [B E]]]. simpl.
      rewrite prepend_path_begin_correct by omega.
      rewrite B.
      specialize (EqR 0). unfold concat_inf in EqR. simpl in EqR.
      rewrite prepend_path_begin_correct in EqR by omega.
      rewrite <-EqR. apply Acc.
    Qed.

    (** In order to prove that r' is final, we prove that infinitely many strings in R' visit a final state.
        This may switch the next string in R', if the final state in run for (W' k) is the last state,
        because this is cut off because it is equal to the first in the run of (W' (S k)). *)
    Lemma string_final_R' k: visits_final (R k) -> visits_final (R' k) \/ visits_final (R' (S k)).
    Proof.
      intros WF. unfold R'. destruct dec_pure_W_final.
      - unfold visits_final.
        destruct W'_transforms.
        destruct compute_run_final_transforms as [? [P [n F]]]. simpl.
        decide (n = S (|w' k|)) as [D|D].
        + right. exists 0. 
          assert (forall y , y 0 = (R (S k)) [0] -> final_state (y 0 )) as T. {
            intros y E. rewrite E. destruct P as [_ [_ H]]. rewrite <-H, <- D. tauto. }
          destruct_in_R'; simpl; split; try omega; unfold path in *; apply T;  tauto.  
        + left. exists n. destruct F. split; oauto.
      - exfalso. apply n. now apply W_final_iff.
    Qed.

    Lemma infinite_final_strings_R: forall n, exists m, m >= n /\ visits_final (R m).
    Proof.
      assert (final (concat_inf R)) as FR. {
        apply final_extensional with (r:= drop (S(|r0|)) r).
        - apply final_drop. apply Acc.
        - intros n. rewrite drop_correct.
          specialize (EqR (S(|r0|) + n)).
          now rewrite prepend_path_rest_correct in EqR by omega. }
      apply (final_concat_inf_infinite_final_strings (aut:=aut) (runs:=R) FR ).
    Qed.

    (** There are infinite final strings in r', so there are infinite final states in r',
       with infinite combinatorics there is a final state occuring infinitely often *)
    Lemma final_r' : final r'.
    Proof.
      unfold r'.
      apply concat_inf_final_step.
      apply concat_inf_is_final_not_constructive.
      intros n.
      destruct (infinite_final_strings_R n) as [m [L P]]; destruct (string_final_R' P).
      - now exists m.
      - exists (S m). split; oauto.
    Qed.  

    (** So we obtain that r' is accepting *)
    Lemma accepting_run_for_W': Sigma r', accepting (aut:=aut) r' ow'.
    Proof.
      exists r'. repeat split; auto using valid_r', initial_r', final_r'.
    Qed.
  
  End Compatibility.       

  Theorem compatibility i j w: ({[i]}o{[j]}^00 /$\ L_B aut) w -> ({[i]}o{[j]}^00) <$= L_B aut.
  Proof.
    intros [wVW [r Acc]] w' w'VW.
    (* To get the accepting run for w', we need to cut everything *)
    apply prepend_on_omega_iteration in wVW.  apply prepend_on_omega_iteration in w'VW.
    destruct wVW as [v [fw [ V [ W E]]]]. destruct w'VW as [v' [fw' [ V' [ W' E']]]].
    
    assert (valid_run r (v +++ concat_inf fw)) as H. {
      apply (valid_run_extensional (r:= r) (w:= w)); auto. apply Acc. }
      
    destruct (partition_run_on_prepend_string H) as [r0 [R' [P1 [P2 [P3 [P4 P5] ]]]]].
    destruct (partition_run_on_concat_inf P5) as [R [P6 [P7 P8]]].

    destruct (accepting_run_for_W' Acc E' V V' W W' (ow:=w) (ow' := w') (r:=r) (v:=v) (v':=v') (w:=fw)(w':=fw') (i:=i)(j:=j) (r0 := r0) (R := R)  ) as [r' A']; auto.
    - intros n. decide (n <= |r0|).
      + rewrite prepend_path_begin_correct by omega.
        specialize (P1 n). now rewrite prepend_path_begin_correct in P1 by omega.
      + rewrite_eq (n = S(|r0|) + (n - S(|r0|))).
        rewrite prepend_path_rest_correct by omega.
        rewrite (P6 (n - S(|r0|))).
        specialize (P1 (S(|r0|) + (n - S(|r0|)))).
        now rewrite prepend_path_rest_correct in P1 by omega.
    - rewrite P3. specialize (P6 0). now rewrite <-P6.
    - now exists r'.
  Qed.

  Corollary compatibilityComplement i j w: ({[i]}o{[j]}^00 /$\ (L_B aut)^$~) w -> ({[i]}o{[j]}^00) <$= (L_B aut)^$~.
  Proof.
    intros [IJw Cw] v IJv Bv. autounfold in *. apply Cw.
    now apply (compatibility (i:=i) (j:=j) (w:=v)).
  Qed.

  Corollary compatibility2 i j: {[i]}o{[j]}^00 <$= L_B aut \/ {[i]}o{[j]}^00 <$= (L_B aut)^$~.
  Proof.
    destruct (dec_language_empty_informative (aut:=(intersect (VW_aut i j) aut) )) as [D|D].
    - left. destruct D as [w'  L]. apply intersect_correct in L.
      apply (compatibility (w:=w') (i:=i)(j:=j)).
      destruct L as [L1 L2]. now apply VW_aut_correct in L1.
    - right. intros w VW.
      autounfold in *. specialize (D w). intros B.
      apply D. apply intersect_correct. split.
      + now apply VW_aut_correct.
      + assumption. 
  Qed.
   
  (** ** Totality [V o W^00] *)

  Section Totality.
    Context (w : Seq A). 

    (** *** Classical Proof using Ramsey
        With Ramsey the proof gets very easy and elegant *)
    Lemma ramseyTotality: (forall (f : nat -> nat -> EquivalenceClassIndex), Ramsey f) -> (exists i j, ({[i]}o{[j]}^00) w).
    Proof.
      intros R.
      destruct (R (fun n m => tilde_eq_class (extract (min n m) (max n m) w))) as [x [g [Inc P]]].
      - intros n m. simpl.
        now rewrite Nat.max_comm, Nat.min_comm.
      - exists (tilde_eq_class (mkstring w (pred (g 1)) )), x, (pred (g 1)). split.
        + apply tilde_eq_class_correct.
        + exists (seq_map (fun n => n - (g 1)) (drop 1 g)). repeat split; unfold seq_map.
          * simpl. intros n. pose (Inc (S n)). destruct n.
            -- omega.
            -- assert (1 <  (S (S n))) as H by omega. assert (1 < S (S (S n))) as H' by omega.   
               pose (s_monotone_strict_order_preserving Inc H).
               pose (s_monotone_strict_order_preserving Inc H'). omega.
          * simpl. omega.
          * intros n.
            pose (Inc 0). rewrite_eq (S (pred (g 1)) = g 1).
            apply equivalent_drop.
            -- repeat rewrite drop_correct. split.
               ++ apply s_monotone_order_preserving; oauto.
               ++ rewrite_eq (1 + S n = S(1 + n)). apply Inc.
            -- repeat rewrite drop_correct.
               rewrite <- (P (1 + n) (1 + S n)) by omega.
               assert (g (1 + n ) <= g (1 + S n)) . { rewrite_eq (1 + S n = S (1 + n)). pose (Inc (1 + n)). omega. }
               rewrite max_r, min_l by auto.
               apply tilde_eq_class_correct.
    Qed.

    (** We now continue using Assumption 2*)
    

    (** *** Equivalence Relation on indices of a Sequence w *)
   
    Notation "k1 '~~@' k2 'at' m" :=((m > k1 /\ m > k2) /\ (extract k1 m w) ~~ (extract k2 m w)) (at level 58).
 
    Instance dec_merge_at k1 k2 m : dec (k1 ~~@ k2 at m).
    Proof. auto. Defined.

    Definition tilde_w_equiv  (k k' : nat) := exists m, k ~~@ k' at m.

    Notation "k1 '~~#' k2" := (tilde_w_equiv k1 k2) (at level 60). 

    Lemma tilde_w_extend k k' m: (k ~~@ k' at m) -> forall m', m' >= m -> k ~~@ k' at m'.
    Proof.
      intros W m' L.
      decide (m = m').
      - now subst m'.
      - split. 
        + omega.
        + apply (tilde_extensional (w:= (extract k m w) ++ (extract m m' w)) (v:= (extract k' m w) ++ (extract m m' w))).
          * now apply tilde_congruence.
          * apply concat_extract; omega.
          * apply concat_extract; omega.
    Qed.

    Lemma tilde_w_index_reflexive k n : k < n -> k ~~@ k at n.
    Proof.
      split.
      - omega.
      - apply tilde_reflexive.
    Qed.  

    Lemma tilde_w_reflexive: reflexive tilde_w_equiv.
    Proof.
      intros s. exists (S s). apply tilde_w_index_reflexive. omega.
    Qed.  
     
    Lemma tilde_w_index_symmetric k1 k2 m: k1 ~~@ k2 at m -> k2 ~~@ k1 at m.
    Proof.
      split.
      - omega.
      - now apply tilde_symmetric.
    Qed.

    Lemma tilde_w_symmetric: symmetric tilde_w_equiv.
    Proof.
      intros s1 s2 [m [P Q]].
      exists m. apply tilde_w_index_symmetric. split;auto. 
    Qed.

    Lemma tilde_w_index_transitive k1 k2 k3 m1 m2:
        k1 ~~@ k2 at m1 -> k2 ~~@ k3 at m2 -> k1 ~~@ k3 at (max m1 m2).
    Proof.
      intros P1 P2. split.
      - split.
        + apply max_le_left. omega.
        + apply max_le_right. omega.
      - apply tilde_w_extend with (m':= max m1 m2) in P1.
        apply tilde_w_extend with (m':= max m1 m2) in P2.
        + destruct P1; destruct P2.
          apply (tilde_transitive (y:= extract k2 (max m1 m2) w)); auto.
        + now apply max_le_right.
        + now apply max_le_left.
    Qed.

    Lemma tilde_w_transitive: transitive tilde_w_equiv.
    Proof.
      intros k1 k2 k3 [m1 P1] [m2 P2].
      exists (max m1 m2).
      apply (tilde_w_index_transitive P1 P2).
    Qed.

    Lemma tilde_w_equivalence : equiv tilde_w_equiv.
    Proof.
     repeat split; auto using tilde_w_reflexive, tilde_w_transitive, tilde_w_symmetric.
    Qed.

    (** *** Excluded Middle for [~~#]
        Because of the unbounded quantifier in [~~#] we cannot decide it. However, we have XM for it *)
    Section PropositionalDecidability.

      Variables k1 k2: nat.

      (* Sequence which is true if [k1 ~~# k2 at n] *)
      Definition tilde_w_equiv_bool := fun n => if (decision (k1 ~~@ k2 at n)) then true else false.

      Lemma tilde_w_index_equiv_iff m : k1 ~~@ k2 at m <-> tilde_w_equiv_bool m = true.
      Proof.
        split; unfold tilde_w_equiv_bool; intros E.
        - now rewrite decision_true by auto.
        - decide (k1 ~~@ k2 at m).
          + auto.
          + discriminate.
      Qed. 

      Lemma tilde_w_equiv_iff: k1 ~~# k2 <-> exists n, tilde_w_equiv_bool n = true.
      Proof.
        split; intros [m E]; exists m; now apply tilde_w_index_equiv_iff.
      Qed.

      Lemma tilde_w_equiv_bool_remains_true m: tilde_w_equiv_bool m = true -> forall n, n >= m -> tilde_w_equiv_bool n = true.
      Proof.
        intros P n L.
        apply tilde_w_index_equiv_iff.
        apply tilde_w_index_equiv_iff in P.
        now apply (tilde_w_extend P).
      Qed. 

      Lemma tilde_w_equiv_bool_infinite_false: infinite false tilde_w_equiv_bool <-> forall n, tilde_w_equiv_bool n = false.
      Proof.
        split.
        - intros Inf n.
          destruct (tilde_w_equiv_bool n ) eqn:H.
          + exfalso. destruct (Inf n) as [m [L F]].
            now rewrite (tilde_w_equiv_bool_remains_true H L) in F.
          + reflexivity.
        - intros F. intros n. exists n. auto.
      Qed.

    End PropositionalDecidability.
    
    Lemma tilde_w_equiv_XM: rel_XM tilde_w_equiv.
    Proof.
      intros k1 k2.
      destruct (finite_type_seq (tilde_w_equiv_bool k1 k2) ) as [[|] Inf].
      - left. apply tilde_w_equiv_iff. destruct (Inf 0) as [k T]. now exists k.
      - right. intros E. apply tilde_w_equiv_iff in E.
        destruct E as [n T].
        destruct (tilde_w_equiv_bool_infinite_false k1 k2) as [F _].
        specialize (F Inf n).
        now rewrite T in F.
    Qed.

    Hint Resolve dupfree_dec.
    Hint Resolve nat_eq_dec.
    Hint Resolve list_exists_dec.

    Lemma not_tilde_w_extend k1 k2: ~ k1 ~~# k2 -> forall m, ~ k1 ~~@ k2 at m.
    Proof.
     intros NE m Em. apply NE. now exists m.
    Qed.

    (** *** [~~#] is of Finite Index *)
  
    Lemma tilde_equiv_finite_index: finiteIndex tilde_equiv.
    Proof.
      exists (Cardinality EquivalenceClassIndex).
      intros L G.
      pose (L' := seq_map (fun w => tilde_eq_class w) L ).
      destruct (can_find_duplicate (|L|) L') as [D|D].
      - destruct D as [i [j [P Q]]]. exists i,j. split; auto.
        apply (equivalent_in_equivalence_class (i := tilde_eq_class (L [i]))).
        + apply tilde_eq_class_correct.
        + unfold L', seq_map in *. simpl in Q. rewrite Q. apply tilde_eq_class_correct.
      - exfalso. omega.
    Qed.

    Lemma tilde_equiv_finite_index_neq: finiteIndexNeg tilde_equiv.
    Proof.
      apply finiteIndexImpliesFiniteIndexNeg. apply tilde_equiv_finite_index.
    Qed.

    Lemma tilde_w_equiv_finite_index_neq : finiteIndexNeg tilde_w_equiv.
    Proof.
      destruct tilde_equiv_finite_index_neq as [n P]. exists n.
      intros L G NE.
      pose (m := S (max_of_nat_string (seq L) (|L|))).
      pose (L' := seq_map (fun k => extract k m w) L).
      apply P with (L:= mkstring L' (|L|)).
      - now simpl.
      - intros x y O E. simpl in O.
        apply (NE x y O). exists m. split.
        + subst m. split.
          * assert (L [x] <= max_of_nat_string (seq L) (| L |)). { apply max_of_nat_string_correct. omega. } omega.
          * assert (L [y] <= max_of_nat_string (seq L) (| L |)). { apply max_of_nat_string_correct. omega. } omega.
        + assumption.
    Qed.

    Lemma tilde_w_equiv_finite_index: finiteIndex tilde_w_equiv.
    Proof.
      apply finiteIndexNegAndXMImpliesFiniteIndex.
      - apply tilde_w_equiv_XM.
      - apply  tilde_w_equiv_finite_index_neq. 
    Qed.

    (** *** Construction of V and W
        We will refine strictly monotone sequences such that in the end the sequence gives the partition of w. *)

    (** There are infinitely many indices such that
        - they are equivalent  *)

    Lemma infinite_equiv_indices : exists g, s_monotone g /\ g 0 > 0 /\ forall n, (g 0) ~~# (g n).
    Proof.
      destruct (finite_equiv_classes tilde_w_equivalence tilde_w_equiv_XM tilde_w_equiv_finite_index (fun n => n)) as [g [Inc E]].
      exists (drop 1 g). repeat split.
      - now apply s_monotone_drop.
      - simpl. now apply s_monotone_ge.
      - intros n. repeat rewrite drop_correct.
        apply (tilde_w_transitive (tilde_w_symmetric (E (1 + 0))) (E (1 + n))).  
    Qed.

    Arguments cc_nat [p] [p_dec] _.

    (** There are infinitely many indices such that
        - they are equivalent
        - the strings [extract (g 0) (g n) w] are equivalent forall n *)

    Lemma infinite_equiv_indices_equiv_begin: exists g, 
           s_monotone g /\ g 0 > 0 /\ (forall n, (g 0) ~~# (g n)) /\ (forall n m, n > 0 -> m > 0 -> extract (g 0) (g n) w ~~ extract (g 0) (g m) w).
    Proof.
      destruct infinite_equiv_indices as [g [GZ [I WE]]].
      pose (g' := fun n => tilde_eq_class (extract (g 0) (g n) w)).
      destruct (finite_type_seq g') as [i Inf].
      pose (f := infinite_filter (P:=fun j => j = i) (fun j => decision (j = i)) Inf ).
      assert (forall n, g' (f n) = i) as H. { intros k. subst f. apply infinite_filter_correct. }
      assert (forall n, n > 0 -> {[i]} (extract (g 0) (g (fix_first_zero f  n)) w)) as H'. {
            intros k Lk. destruct k.
            - exfalso. omega.
            - specialize (H (S k)). unfold g' in H. unfold fix_first_zero.
              rewrite <-H. apply tilde_eq_class_correct. } 
      exists (fun n => g (fix_first_zero f n)). split.
      - unfold f. auto using compose_s_monotone, fix_first_zero_s_monotone, infinite_filter_s_monotone.
      - split; [|split] .
        + now apply s_monotone_ge_zero.  
        + intros n. simpl. apply WE.
        + intros n m Ln Lm. simpl.
          apply equivalent_in_equivalence_class with (i:=i); now apply H'.
     Qed.

     (** There are infinitely many indices such that
         - they are equivalent
         - the strings [extract (g 0) (g n) w] are equivalent forall n
         - for all j<=i we have [(g j) ~~@ (g i) at (g (S i))] *)

     Definition merge_at_next (w: String nat) := forall i j, j<=i < |w| -> w [j] ~~@ w[i] at (w [S i]).

     Instance dec_merge_at_next: forall w, dec(merge_at_next w).
     Proof.
        intros v. unfold merge_at_next.
        enough (dec (forall i,  i < |v| -> (forall j, j <= i -> v[j]~~@ v[i] at (v[S i])))) as [H|H].
        - left.  intros i j L. apply H; omega.
        - right. intros N. apply H. intros i L j L'. apply N; omega.
        - auto.
     Defined.
    
     Lemma merge_at_next_extensional v v': merge_at_next v ->  v == v' -> merge_at_next v'.
     Proof.
       intros M  [E1 E2] i j L.
       rewrite <-E1 in L. specialize (M i j L). split.
       - destruct M as [M M']. now repeat rewrite <-E2 by omega.
       - apply (tilde_extensional (w:= extract (v [j]) (v [S i]) w) (v:= (extract (v [i]) (v [S i]) w))).
         + apply M.
         + split; intros *; simpl; repeat rewrite E2 by omega; oauto.
         + split; intros *; simpl; repeat rewrite E2 by omega; oauto.
     Qed.

     Lemma common_merge_index g g' : g' 0 = 0 -> (forall n : nat, g 0 ~~# g n) -> forall k, exists m, forall i, i <= k -> g 0 ~~@ g (g' i) at m.
     Proof.
       intros Z WE k.
       induction k.
       - exists (S (g 0)). intros i L. rewrite_eq (i = 0). rewrite Z.  apply tilde_w_index_reflexive. omega.
       - destruct IHk as [m P]. destruct (WE (g' (S k))) as [m' Q].
         exists (max m m'). intros i L.
         pose (Nat.le_max_r m m'); pose (Nat.le_max_l m m'). decide (i = S k). 
         + subst i. apply tilde_w_extend with (m := m'); auto.
         + apply tilde_w_extend with (m := m); try(apply P); oauto.
     Qed.

     Lemma merge_at_next_append g g' m : s_monotone g -> merge_at_next (substring g g')-> m > g' [| g' |] -> (forall i,  i < |g'| -> g (g' [i]) ~~@ g (g' [|g'|]) at (g m))
             ->   merge_at_next (substring g (g' ++ mkstring (fun _ : nat => m) 0)).
     Proof.
       intros Inc M G MS i j.
       decide (i = |g'|); intros O; simpl in *.
       - subst i. rewrite_eq (S(|g'|) = S(|g'|) + 0). rewrite prepend_path_rest_correct.
         repeat rewrite prepend_path_begin_correct by omega.
         decide (j = |g'|).
         + subst j. apply tilde_w_index_reflexive. simpl. apply s_monotone_strict_order_preserving; auto.
         + apply MS. omega.
       - repeat rewrite prepend_path_begin_correct by omega.
         apply tilde_w_extend with (m:= g(g' [S i])).
         + apply M. simpl. omega.
         + omega. 
     Qed.

     Lemma there_is_bigger_merging_index g: s_monotone g -> (forall n, (g 0) ~~# (g n)) ->
           forall g', g' [0] = 0 -> merge_at_next (substring g g') -> exists m, m > g' [| g' |] /\ merge_at_next (substring g (g' ++ mkstring (fun _ : nat => m) 0)). 
     Proof. 
       intros Inc WE [g' l] Z M. induction l.
       - simpl. exists (S (g' 0)). split.
         + omega.
         + apply merge_at_next_append; auto; simpl. intros i L . omega.
       - destruct (common_merge_index Z  WE (S l)) as [m P].
         destruct (s_monotone_unbouded Inc m) as [k Q].
         assert (g k > g' (S l)) as H. { destruct (P (S l)) as [H _]. { omega. } simpl in H. pose (s_monotone_ge Inc (g' (S l))). omega. }
         exists (g k). split.
         + auto. 
         + apply merge_at_next_append; auto.
           simpl. intros i G. simpl in *.
           apply tilde_w_extend with (m:=m).
           * assert (max m m = m) as H' by now apply max_l. rewrite <-H'.
             apply (tilde_w_index_transitive (k1:=g(g' i)) (k2:=g 0) (k3:=g(g' (S l))) (m1 := m) (m2 := m)).
             -- apply tilde_w_index_symmetric. apply P. omega.
             -- apply P. omega.
           * pose (s_monotone_order_preserving Inc Q). pose (s_monotone_ge Inc m). omega.
     Qed.

     Lemma infinite_equiv_indices_merging: exists g, s_monotone g /\ g 0 > 0 /\
           (forall n, (g 0) ~~# (g n)) /\ (forall n m, n > 0 -> m > 0 -> extract (g 0) (g n) w ~~ extract (g 0) (g m) w) /\
           (forall j i, j <= i -> (g j) ~~@ (g i) at (g (S i))).
     Proof.
       destruct infinite_equiv_indices_equiv_begin as [g [Inc [GZ [WE BE]]]].
       assert (merge_at_next (mkstring g 0)) as baseP. {intros i j L. simpl in L. exfalso. omega. }
       pose (stepP := there_is_bigger_merging_index Inc WE).
       assert (s_monotone (history_filter dec_merge_at_next merge_at_next_extensional baseP stepP)) as Inc2 by apply history_filter_s_monotone.
       exists (fun n => g (history_filter dec_merge_at_next merge_at_next_extensional baseP stepP n)). split.
       - apply compose_s_monotone; auto.
       - split; [|split]; [| |split].
         + now apply s_monotone_ge_zero.
         + intros n. rewrite history_filter_zero. apply WE.
         + intros n m Ln Lm. repeat rewrite history_filter_zero. apply BE.
           -- pose (s_monotone_ge Inc2 n). omega.
           -- pose (s_monotone_ge Inc2 m). omega.
         + intros j i L. split.
           -- split; apply s_monotone_strict_order_preserving; auto;  apply s_monotone_strict_order_preserving; oauto.
           -- specialize (history_filter_correct dec_merge_at_next merge_at_next_extensional baseP stepP (S i)).
              intros E. specialize (E i j). simpl in E. apply E. omega.
    Qed.

    (** Finally we can give the desired V and W *)

    Lemma totality: exists i j, ({[i]}o{[j]}^00) w.
    Proof.
      destruct infinite_equiv_indices_merging as [g [Inc [GZ [WE [BE M]]]]].
      exists (tilde_eq_class (extract 0 (g 0) w)), (tilde_eq_class (extract (g 0) (g 1) w)), (pred (g 0)).
      split.
      - unfold extract. simpl. rewrite_eq (pred (g 0) = g 0 -1). apply tilde_eq_class_correct.
      - rewrite_eq (S (pred (g 0)) = g 0).
        exists (fix_first_zero (seq_map (fun n => n - g 0 ) g)). split.
        + apply fix_first_zero_s_monotone. intros n. destruct n; simpl; unfold seq_map. 
          * specialize (Inc 0). omega.
          * pose (s_monotone_strict_order_preserving Inc (k:=0) (n:= S n) ).
            pose (s_monotone_strict_order_preserving Inc (k:=0) (n:= S (S n)) ).
            pose (Inc (S n)).  omega.  
        + split.
          * reflexivity.
          * intros n. unfold seq_map. simpl. destruct n; simpl.
            -- unfold extract. simpl. rewrite_eq (g 1 - g 0 - 1 = g 1 - S(g 0)). apply tilde_eq_class_correct.
            -- apply equivalent_drop. { split.
                  - apply s_monotone_order_preserving; oauto.
                  - apply Inc. }
               destruct (M 0 (S n) ) as [_ M']. { omega. }
               assert (1 > 0) as H' by omega. assert (S (S n) > 0) as H'' by omega.
               specialize (BE 1 (S (S n)) H' H'').
               apply (equivalence_class_closed (tilde_eq_class_correct ((extract (g 0) (g 1) w)) )).
               apply tilde_symmetric.
               apply (tilde_transitive BE M').
    Qed.

  End Totality.

  (** ** Definition of the Complement Buechi NFA *)
  Section Complement.

    (** NFAs recognizing all [V o W^00]*)
    Definition VW := EquivalenceClassIndex (x) EquivalenceClassIndex.
           
    (** [V o W^00] is part of the complement if its intersection with the Buechi language is empty *)
    Definition VW_part_of_complement (vw : VW) := L_B (intersect (VW_aut (fst vw) (snd vw)) aut) =$= {}.
    
    Instance dec_VW_part_of_complement vw: dec (VW_part_of_complement vw).
    Proof.
     unfold VW_part_of_complement.
     apply dec_language_empty.
    Qed.

    Definition complement_auts := map (fun vw => VW_aut (fst vw) (snd vw)) (filter (DecPred VW_part_of_complement  ) (elem VW)). 
   
    (** The complement automaton is the union of all these automata *)
    Definition autC := fold_right union empty_aut complement_auts.
    
    (** *** Correctness Lemmata *)
    Lemma autC_disjoint: L_B aut /$\ L_B autC =$= {}.
    Proof.
      apply language_empty_iff. intros w [LA LC].
      destruct (totality w) as [i [j P]].
      unfold autC in LC. apply many_aut_union in LC. destruct LC as [b [IC LB]].
      unfold complement_auts in IC. apply in_map_iff in IC. destruct IC as [vw [AVW Q]].
      apply in_filter_iff in Q.  destruct Q as [Q1 Q2].
      apply (Q2 w).
      apply intersect_correct. split.
      - now rewrite AVW.
      - assumption.
    Qed.

    Lemma part_of_complement_implies_complement i j: VW_part_of_complement (i,j) -> {[i]}o{[j]}^00 <$= L_B autC.
    Proof.
     intros PC w VW.
     apply many_aut_union.
     exists (VW_aut i j). split.
     - unfold complement_auts.
       apply in_map_iff.
       exists (i,j). split;auto.
       apply in_filter_iff. split.
       + apply elementIn.
       + unfold VW_part_of_complement. simpl.
         apply language_empty_iff. intros w' L. now apply (PC w').
     - now apply VW_aut_correct.
    Qed.

    Lemma not_part_of_complement_implies_aut i j: ~VW_part_of_complement (i,j) -> {[i]}o{[j]}^00 <$= L_B aut.
    Proof.
     intros nPC w VW.
     unfold VW_part_of_complement in nPC. 
     destruct (dec_language_empty_informative (aut:=(intersect (VW_aut i j) aut) )) as [D|D].
     - destruct D as [w'  L]. apply intersect_correct in L.
       apply (compatibility (w:=w') (i:=i)(j:=j)).
       + destruct L as [L1 L2]. now apply VW_aut_correct in L1.
       + assumption.
     - exfalso. auto. 
    Qed.

    Lemma complement_complete : L_B autC \$/ L_B aut =$= A^0$0.
    Proof.
     apply language_universal_iff. intros w.
     destruct (totality w) as [i [j P]].  
     decide (VW_part_of_complement (i,j)) as [D|D].
     - left. now apply (part_of_complement_implies_complement D).
     - right. now apply (not_part_of_complement_implies_aut D).
    Qed.


    Lemma complement_correct: L_B autC =$= (L_B aut)^$~.
    Proof.
      intros w. destruct (complement_complete w). pose (autC_disjoint w).
      autounfold in *. tauto.
    Qed.

    Lemma complement_correct2: (L_B autC)^$~ =$= L_B aut.
    Proof.
      intros w. destruct (complement_complete w). pose (autC_disjoint w).
      autounfold in *. tauto.
    Qed.

    Definition complement := autC.
  
  End Complement.

End TildeEquivalenceRelation.

(** ** Decision Corallaries *)
Section ComplementCorollaries.

   Context {A: finType}.

   Corollary dec_language_universal (aut:BuechiAut A) : dec(L_B aut =$= A^0$0).
   Proof.
    destruct (dec_language_empty (aut:= (complement (aut:= aut)))) as [D|D].
    - left. apply language_universal_iff. intros w. specialize (D w).
      destruct (complement_complete (aut:=aut) w). autounfold in *. tauto.
    - right. intros L. apply D. intros w. pose (complement_correct2 (aut:=aut) w).
      autounfold in *. specialize (L w). tauto.
   Qed.

   Corollary dec_language_inclusion (aut1 aut2:BuechiAut A): dec (L_B aut1 <$= L_B aut2).
   Proof.
     destruct (dec_language_empty (aut:= (intersect aut1 (complement (aut:= aut2))))) as [D|D].
     - left. intros w L. specialize (D w).
       destruct (complement_complete (aut:=aut2) w) as [_ [D'| D']].
       + auto. 
       + exfalso. apply D. now apply intersect_correct.
       + assumption.
     - right. intros I. apply D. apply language_empty_iff.
       intros w L. apply intersect_correct in L. destruct L as [L1 L2].
       apply complement_correct in L2. auto.
   Qed.

   Corollary dec_language_eq (aut1 aut2:BuechiAut A): dec (L_B aut1 =$= L_B aut2).
   Proof.
     pose (language_eq_iff (L_B aut1) (L_B aut2)) as P.
     apply dec_trans with (P:=language_inclusion (L_B aut1) (L_B aut2) /\ language_inclusion (L_B aut2) (L_B aut1)).
     - auto using and_dec, dec_language_inclusion.
     - split; apply language_eq_iff.
   Qed.

End ComplementCorollaries.
