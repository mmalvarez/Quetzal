Set Implicit Arguments.
Require Import BA.External.
Require Import BA.FinTypes.
Require Import Coq.Init.Nat.
Require Import BasicDefs.
Require Import Seqs.
Require Import StrictlyMonotoneSeqs.
Require Import SeqOperations.
Require Import NFAs.
Require Import Utils.

Open Scope string_scope.

(** ** Necessary Assumption to formalize Buechi automata *)
Section NecessaryAssumptions.

  (** A relation has XM property *)
  Definition rel_XM (X:Type) (R: X -> X-> Prop) := forall x y, R x y \/ ~ R x y.
  (** A relation over X is of finite index if there is a number n, such that all strings of elements of X
     longer then n contains at least two different positions which are in the relation *)
  Definition finiteIndex (X:Type) (R: X -> X -> Prop) := (exists n, forall (L : String X), |L| > n -> exists i j, i < j <= |L| /\ R (L[i]) (L[j])).
  Definition finiteIndexNeg(X:Type) (R: X -> X -> Prop) := (exists n, forall (L:String X), |L| > n -> (forall i j, i < j <= |L| -> ~ (R (L[i]) (L[j]))) -> False ).

  (** *** Assumption 1: Sequences over Finite Types
     A sequence over a finite type contains one member of the type infinitely often. *)
  Definition FiniteTypeSeq (X:finType): Prop := forall  (f: Seq X), exists (x:X), infinite x f.

  (** *** Assumption 2: Given a XM equivalence relation with finite index on X, then for every
         sequence over X there is a subsequence those members are all equivalent *)
  Definition FiniteEquivClasses (X :Type) (R : X -> X -> Prop) : Prop := equiv X R -> rel_XM R -> finiteIndex R ->
                                      forall (f: Seq X), exists (g: Seq nat), s_monotone g /\ (forall n, R (f (g 0)) (f (g n))).

  Definition Ramsey (X:finType) (f: nat -> nat -> X) : Prop := (forall n m, f n m = f m n) -> exists (x: X) (g: Seq nat), s_monotone g /\ forall n m, n <> m -> f (g n) (g m) = x. 

  (** Assumption 1 can be derived from Assumption 2 *)

  Lemma finTypeEqRelXM (X:finType) : rel_XM (fun (x y:X) => x = y).
  Proof.
    intros x y.  decide (x = y); tauto.
  Qed.
  Arguments finTypeEqRelXM  _ _ _ : clear implicits.

  Lemma finTypeEqEquiv (X:finType) : equiv X (fun (x y:X) => x = y).
  Proof.
    repeat split.
    - intros x y z A B. now rewrite A.
    - intros x y A. now symmetry.
  Qed.

  Lemma finTypeEqFiniteIndex (X:finType) : finiteIndex (fun (x y :X) => x = y).
  Proof.
    exists (Cardinality X).
    intros L G.
    destruct (can_find_duplicate (|L|) (seq L)) as [[i [j [P Q]]]|D].
    - exists i,j. auto.
    - exfalso. omega.
  Qed. 

  Lemma finEquivClassesImpliesFiniteTypeSeq: (forall X (R: X -> X -> Prop), FiniteEquivClasses R)  -> (forall X, FiniteTypeSeq X).
  Proof.
    intros FE X f.
    destruct (FE X (fun (x y : X) => x = y) (finTypeEqEquiv X) (finTypeEqRelXM X) (finTypeEqFiniteIndex X) f) as [g [M E]].
    exists (f (g 0)).
    intros n. destruct (s_monotone_unbouded M n) as [m P].
    exists (g m). auto.
  Qed.

  (** Assumption 1 can be derived from Ramsey using only two colors*)
  Lemma ramseyImpliesFiniteTypeSeq: (forall  (f: nat->nat -> finType_bool), Ramsey f) -> (forall X, FiniteTypeSeq X).
  Proof.
    intros R X. intros f.
    specialize (R (fun n m => if (decision (f n = f m)) then true else false)).
    destruct R as [x [g [P Q]]].
    - intros n m. simpl. decide (f n = f m).
      + now rewrite decision_true.
      + rewrite decision_false; auto.
    - destruct x.
      + exists (f ( g 0)).
        intros n. 
        exists (g (S n)); split.
        * pose (s_monotone_ge P n). pose (P n). omega.
        * assert (S n <> 0) as H by congruence.
          specialize (Q (S n) 0 H). decide ((f (g (S n)) = f (g 0))).
          -- trivial.
          -- discriminate Q.
      + exfalso.
        destruct (can_find_duplicate (S (Cardinality X)) (fun n => f ( g n))) as [[n1 [n2 [H1 H2]]]| H].
        * assert (n1 <> n2) as H3 by omega.
          specialize (Q n1 n2 H3).
          now rewrite decision_true in Q by auto.
        * omega.
  Qed. 

  (** For some equivalence relations, we can derive Assumption 2 from Assumption 1 *)
  Lemma decFinEquivRel_FiniteTypeSeqImpliesFinEquivClasses (X: Type) (F: finType): FiniteTypeSeq F ->
      forall (R: X -> F), FiniteEquivClasses (fun (x y: X) => R x = R y).
  Proof.
    intros FS R _ _ _ f.
    destruct (FS (seq_map R f) ) as [a Inf].
    pose (P:= fun x => R x = a).
    assert (forall x, dec( P x)) as decP. { intros y. unfold P. auto. }
    exists (infinite_filter decP Inf). split.
    - apply infinite_filter_s_monotone.
    - intros n. pose (infinite_filter_correct decP Inf) as H. simpl in H.
      now repeat rewrite H.
  Qed.

  (** Then for the same equivalence relations, Assumption 2 can be derived from Ramsey with two colors*)
  Lemma decFinEquivRel_RamseyImpliesFinEquivClasses (X: Type) (F: finType): (forall  (f: nat->nat -> finType_bool), Ramsey f) ->
      forall (R: X -> F), FiniteEquivClasses (fun (x y: X) => R x = R y).
  Proof.
    intros R.
    apply decFinEquivRel_FiniteTypeSeqImpliesFinEquivClasses.
    now apply ramseyImpliesFiniteTypeSeq.
  Qed.

  (** Nevertheless we mark both assumptions as axioms. So Coq can tell whether a lemma only depends
      on the weaker Assumption 1. Ramsey is not an axiom. *)
  Axiom finite_type_seq: forall X, FiniteTypeSeq X.

  Axiom finite_equiv_classes: forall X (R:X->X->Prop), FiniteEquivClasses R.

  (** Assumption 1 can be generalized to predicates on finite type *)
  Lemma finite_type_predicate_seq (X:finType) (P: X -> Prop) (decP: forall x, dec(P x)):
       forall (f: Seq X), (forall n, exists m, m >= n /\ P (f m)) -> (exists (x:X), infinite x f /\ P x).
  Proof.
    intros f InfP.
    destruct (finite_type_seq  (fun n => f ((infinite_filter decP InfP) n))) as [x Inf].
    exists x. split.
    - intros n. destruct (Inf n) as [m [L Pm]].
      exists (infinite_filter decP InfP m). split.
      + assert (infinite_filter decP InfP m >= m). { apply s_monotone_ge. apply infinite_filter_s_monotone. } omega.
      + assumption.
    - destruct (Inf 0) as [m [L Pm]]. rewrite <-Pm. apply infinite_filter_correct.
  Qed.

  Lemma finiteIndexImpliesFiniteIndexNeg (X: Type) (R: X -> X -> Prop): finiteIndex R -> finiteIndexNeg R.
  Proof.
    unfold finiteIndex. intros [n P]. exists n. firstorder.
  Qed.

  Lemma finiteIndexNegAndXMImpliesFiniteIndex (X: Type) (R: X -> X -> Prop): rel_XM R -> finiteIndexNeg R -> finiteIndex R.
  Proof.
    unfold finiteIndex, rel_XM. intros XM. 
    intros [n P]. exists n. intros L G.
    enough ((exists i j, i < j <= | L | /\ R (L [i])  (L [j])) \/ (forall i j, i < j <= |L| -> ~ R (L[i])( L[j]))) as [H|H].
    - assumption.
    - exfalso. firstorder.
    - clear G. destruct L as [L l]. simpl. induction l. 
      + right. intros i j O. exfalso. omega.
      + destruct IHl as [[i [j [O E]]] | IHl].
        * left. exists i; exists j. split; oauto.
        * { enough ((exists k, k <= l /\ R (L k) ( L (S l))) \/ (forall k, k <=  l -> ~ R (L k)( L (S l)))) as [[k [O E]] | H]. 
            - left. exists k; exists (S l). split; oauto.
            - right. intros i j O E.
                decide (j = S l) as [D|D].
                * apply (H i). omega. now rewrite <-D .
                * apply (IHl i j);oauto.
            - apply seq_prop_dec_exists_bounded with (p:= (fun k => R k  (L(S l)))). 
              intros k. apply XM. }
  Qed.

End NecessaryAssumptions.
  

(** * Buechi Acceptance for Sequences on NFAs *)
Section BuechiLanguage.
 
  Variable A : finType.
  Definition BuechiAut := NFA A.

  Definition initial (aut: BuechiAut) (r: Run aut) := initial_state (r 0).
  Definition final (aut: BuechiAut) (r: Run aut) := exists s, infinite s r /\ (final_state s). 
  Definition accepting (aut:BuechiAut) (r:Run aut) (w: Seq A) := (valid_run r w) /\ (initial r) /\ (final r).
  Definition language (a:BuechiAut):SeqLang  A:= fun  (w: Seq A) => exists (r:Run a), accepting r w.

  Lemma infinite_final_is_accepting_for_finite_automaton (aut: BuechiAut) (r: Run aut)  :
     (forall n, exists m, m>=n /\ (final_state (r m))) -> final r.
  Proof.
    intros F.
    destruct (finite_type_predicate_seq (final_state_dec (aut:=aut)) F) as [s [I Fs]].
    exists s. auto.
  Qed.  

  Lemma final_drop (a:BuechiAut) (r:Run a) n : final r -> final (drop n r).
  Proof.
    intros [s [I F]].
    exists s. split; auto.
    now apply drop_preserves_finite.
  Qed.

  Lemma final_prepend (a:BuechiAut) (r1 r2:Run a) n : final r1 -> final (prepend_path n r2 r1).
  Proof.
    intros [s [I F]].
    exists s. split ;auto. 
    intros k.
    destruct (I k) as [x [P Q]].
    exists (x + S n). split.
    - omega.
    - rewrite (prepend_path_rest_correct2 r2 r1 (n:=x)); oauto.
  Qed.

  
  Lemma final_extensional (a:BuechiAut) (r r' :Run a): final r -> r === r' -> final r'.
  Proof.
    intros [s [I F]] E.
    exists s. split; auto.
    intros n.
    destruct (I n) as [m [ P Q]].
    exists m. split;auto.
    now rewrite <-E.
  Qed.
 
End BuechiLanguage.

Notation "'L_B'" := language.


(** ** Simple Example: NFA recognizing the Buechi language [(ab)^00] *)

Module BuechiExample.

  (** Use local notations to avoid declaring extra finite types *)
  Definition alphabet := ? finType_unit.
  Notation "'a'" := (Some tt).
  Notation "'b'" := None .
  
  Definition state := finType_bool.
  Notation "'S1'" := true.
  Notation "'S2'" := false.

  (** Easy definition of the language to recognize *)

  Definition ab_omega :SeqLang alphabet:= fun w=>  (w 0) = a /\ forall n, ((w n) = a -> (w (S n)) = b) /\ ((w n) = b -> (w (S n)) = a).
  
  (** Definition of the automaton *)

  Definition transition s1 l s2:= match s1,l with
     |S1, a => s2 = S2
     |S2, b => s2 = S1
     |_,_ => False
   end.
 
  Lemma dec_transition s1 l s2: dec (transition s1 l s2).
  Proof.
    destruct s1,l as [[]|],s2; simpl; auto.
  Qed.
  
  Definition initial_state (s:state) := s = S1.
  Definition final_state (s:state) := True.

  Lemma dec_initial_state s: dec(initial_state s).
  Proof.
   destruct s; unfold initial_state; auto. 
  Qed.

  Lemma dec_final_state s: dec(final_state s).
  Proof.
   left. exact I.
  Qed.

  Definition aut := mknfa dec_transition  dec_initial_state dec_final_state.

  (** Correctness proof *)

  Lemma ab_omega_incl_aut: ab_omega <$= L_B aut .
  Proof.
   intros w ABo.
   pose (r:= (fix f n := match n with
            |0 => S1 
            | (S n) => match (f n) with
                | S1 => S2
                | S2 => S1 end end) ).
   exists r. repeat split.
   - intros n. induction n.
     + destruct ABo as [ABo _].
       now rewrite ABo.
     + destruct ABo as [_ ABo]. simpl in IHn. destruct (w n) as [[ ]| ] eqn:H1, (r n)  eqn:H2; simpl in *.
       * rewrite H2.
         assert (w (S n) = b) as H3. { apply ABo. assumption. }
         now rewrite H3.
       * exfalso. apply IHn.
       * exfalso. apply IHn.
       * rewrite H2.
         assert (w (S n) = a) as H3. { apply ABo. assumption. }
         now rewrite H3.
  - exists S1. split.
    + intros n. destruct (r n) eqn:H; [ (exists (S(S n))) | exists (S n)] ; split;
      try omega; try simpl; now rewrite H.
    + reflexivity.
  Qed.
  
  Lemma aut_incl_ab_omega: L_B aut <$= ab_omega.
  Proof.
    intros w [r [V [I A]]]. split.
    - unfold initial in I. simpl in I. unfold initial_state in I.
      specialize (V 0). rewrite I in V. simpl in V.
      destruct (w 0) as [[]|]; tauto.
    - intros n. destruct (w n) as [[]|] eqn:Hw.
      + split.
        * intros _.
          pose (Vn := (V n)). simpl in Vn. rewrite Hw in Vn.
          specialize (V (S n)).
          destruct (r n); destruct (r (S n)); destruct (w (S n)) as [[]|]; simpl in *; auto; try tauto.
          discriminate Vn.
        * intros E. discriminate E.
      + split.
        * intros E. discriminate E.
        * intros _.
          pose (Vn := (V n)). simpl in Vn. rewrite Hw in Vn.
          specialize (V (S n)).
          destruct (r n); destruct (r (S n)); destruct (w (S n)) as [[]|]; simpl in *; auto; try tauto.
          discriminate Vn.
  Qed.
 
  Goal ab_omega =$= L_B aut.
  Proof.
   split.
   - apply ab_omega_incl_aut.
   - apply aut_incl_ab_omega. 
  Qed.

  (** Remark: With the constructions in NFAConstructions this would be easier, because one only needs to
      build an NFA recognizing the string language [ab], but as a first example this serves better. *)

End BuechiExample.

(** ** NFA with empty Buechi language *)
Section EmptyAut.
  
  Context {A:finType}.
  Definition empty_state := finType_False.

  Definition no_state (s : empty_state) := False.
  Definition no_transition (s : empty_state) (a:A) (s' : empty_state) := False.

  Instance dec_no_state s : dec(no_state s). Proof. auto. Qed.
  Instance dec_no_transition s a s' : dec (no_transition s a s'). Proof. auto. Qed.

  Definition empty_aut := mknfa dec_no_transition dec_no_state dec_no_state.

  Lemma empty_aut_correct: L_B empty_aut =$= {}.
  Proof.
   apply language_empty_iff. intros w L.
   destruct L as [r [? [I ?]]].
   unfold initial in I. simpl in I. contradiction I.
  Qed.

  Lemma seq_in_empty_aut_contradicts w: L_B empty_aut w -> False.
  Proof.
    intros B.
    pose (P := empty_aut_correct w). now apply P.
  Qed.
End EmptyAut.

(** ** Closure under Union of Buechi languages *) 
Section Closed_Union.

  Context {A : finType}. 

  Variable aut1: BuechiAut A.
  Variable aut2: BuechiAut A.
  
  (** *** Definition of the union automaton 
 
      Just stick the two automata together and prohibit, that the new 
      automata can switch from the states of one to the states of the other. *)
  
  Definition union_state : finType := (state aut1) (+) (state aut2).
  Definition union_transition (s1:union_state) (a:A) (s2:union_state) := match s1,s2 with
            | (inl s1), (inl s2) => transition s1 a s2
            | (inr s1), (inr s2) => transition s1 a s2
            | _ , _ => False
           end.
  Definition union_initial (s:union_state) := match s with
            | inl s => initial_state s
            | inr s => initial_state s
           end.
  Definition union_final (s : union_state) :=match s with
            | inl s => final_state s
            | inr s => final_state s
           end.
  Lemma dec_union_transition: forall s1 a s2, dec(union_transition s1 a s2).
  Proof.
   intros s1 a s2. destruct s1,s2; simpl; auto.
  Qed.

  Lemma dec_union_initial: forall s, dec(union_initial s).
  Proof.
    intros s. destruct s; auto.
  Qed.

  Lemma dec_union_final: forall s, dec(union_final s).
  Proof.
    intros s. destruct s; simpl; auto.
  Qed.

  Definition autU:= mknfa dec_union_transition dec_union_initial dec_union_final.

  (** *** Proving Correctness
      This is slightly redundant since the union automaton is symmetric in aut1 and aut2.
      But exploiting this symmetry is more effort. *)

  (** Because states from aut1 can only go the states of aut1 and the same for aut2, a valid run on
     autU has either only states of aut1 or only states of aut2 *)
  Lemma states_do_not_mix: forall (w:Seq A) (r : Run autU), (valid_run (aut:=autU) r w) ->(forall n, exists (s : state aut1), r n = inl s) \/ (forall n, exists (s:state aut2), r n = inr s).
  Proof.
   intros w r V.
   destruct (r 0) as [s|s] eqn :H.
   - left. induction n.
     + firstorder.
     + specialize (V n). simpl in V.
       destruct IHn as [s1 E]. rewrite E in V.
       destruct (r (S n)) as [s2|s2].
       * now exists s2.
       * contradiction V.
   - right.
     induction n.
     + firstorder.
     + specialize (V n). simpl in V.
       destruct IHn as [s1 E]. rewrite E in V.
       destruct (r (S n)) as [s2|s2].
       * contradiction V.
       * now exists s2.
  Qed.

  (** Given an accepting run of the union aut, the final states decides whether the sequence
      is accepted by aut1 or aut2 *)

  Lemma autU_accepted_by_aut1 (w:Seq A):
      (exists r, (valid_run (aut:=autU) r w) /\ (initial r) /\ 
        (exists (s: state aut1), infinite (inl s) r /\ (final_state (aut:=autU) (inl s))))
      -> (L_B aut1 w).
  Proof.
  intros [r [V [I [sf [Inf_s Final_s]]]]].
  destruct (states_do_not_mix  V) as [M|M].
  - exists (fun n => match r n with
            | inl s' => s'
            | inr _ => sf
            end). repeat split.
    + intros n.
      destruct (M n) as [s1 E1]. destruct (M (S n)) as [s2 E2].
      specialize (V n).
      rewrite E1, E2 in V. simpl in V.
      now rewrite E1, E2.
    + destruct (M 0) as [s0 E0]. unfold initial in *.
      rewrite E0. rewrite E0 in I.
      now simpl in I.
    + exists sf. split; auto.
      intros n. destruct (Inf_s n) as [m [P Q]].
      exists m. split; auto. now rewrite Q.
  - exfalso.
    destruct (Inf_s 0) as [m [P Q]]. destruct (M m) as [s0 E0].  
    now rewrite Q in E0.
  Qed.

  Lemma autU_accepted_by_aut2 (w:Seq A):
      (exists r, (valid_run (aut:=autU) r w) /\ (initial r) /\ 
        (exists (s: state aut2), infinite (inr s) r /\ (final_state (aut:=autU) (inr s))))
      -> (L_B aut2 w).
  Proof.
  intros [r [V [I [sf [Inf_s Final_s]]]]].
  destruct (states_do_not_mix  V) as [M|M].
  - exfalso.
    destruct (Inf_s 0) as [m [P Q]]. destruct (M m) as [s0 E0].  
    now rewrite Q in E0.
  - exists (fun n => match r n with
            | inr s' => s'
            | inl _ => sf
            end). repeat split.
    + intros n.
      destruct (M n) as [s1 E1]. destruct (M (S n)) as [s2 E2].
      specialize (V n).
      rewrite E1, E2 in V. simpl in V.
      now rewrite E1, E2.
    + destruct (M 0) as [s0 E0]. unfold initial in *.
      rewrite E0. rewrite E0 in I.
      now simpl in I.
    + exists sf. split; auto.
      intros n. destruct (Inf_s n) as [m [P Q]].
      exists m. split; auto. now rewrite Q.
  Qed.

  Lemma aut1_incl_autU: L_B aut1 <$= L_B autU.
  Proof.
    intros w [r [V [I [ sf [Inf_s Final_s]]]]].
    exists (fun n => inl (r n)). repeat split; auto.
    exists (inl sf). split; auto.
    intros n. destruct (Inf_s n) as [m [P Q]].
  exists m. split;auto. now rewrite Q.
  Qed.

  Lemma aut2_incl_autU: L_B aut2 <$= L_B autU.
  Proof.
    intros w [r [V [I [ sf [Inf_s Final_s]]]]].
    exists (fun n => inr (r n)). repeat split; auto.
    exists (inr sf). split; auto.
    intros n. destruct (Inf_s n) as [m [P Q]].
  exists m. split;auto. now rewrite Q.
  Qed.

  Lemma closed_union: Sigma autU, L_B autU =$= L_B aut1 \$/ L_B aut2.
  Proof.
   exists autU. intros w. split.
   - intros [r [V [I [[s|s] [Inf_s Final_s]]]]].
     + left.  apply autU_accepted_by_aut1. firstorder.
     + right. apply autU_accepted_by_aut2. firstorder.
   - intros [L1 | L2].
     + now apply aut1_incl_autU.
     + now apply aut2_incl_autU.
  Qed.

  Definition union:= projT1 (closed_union).
  
  Lemma union_correct: L_B union =$= L_B aut1 \$/ L_B aut2.
  Proof.
    unfold union. now destruct closed_union.
  Qed.

End Closed_Union.

(** Union of finitely many NFAs *)
Lemma many_aut_union (A:finType) (l:list (BuechiAut A)) w:
             L_B (fold_right union empty_aut l) w <->  exists a, (a el l) /\ L_B a w.
Proof.
split.
- intros U.
  induction l.
  + simpl in U. exfalso. apply (seq_in_empty_aut_contradicts U).
  + simpl in U.
    apply union_correct in U.
    destruct U as [U|U].
    * exists a; auto.
    * destruct (IHl U) as [a' [H1 H2]].
      exists a'; split; auto.
- intros [b [I L]].
  induction l.
  + contradiction I.
  + simpl. apply union_correct.
    destruct I as [I |I].
    * left. now rewrite I.
    * right. now apply IHl.
Qed.

(** ** Closure under Intersection of Buechi languages *)
Section Closed_Intersection.

  Lemma leq_to_distance (X:Type) (p : X->Prop) (w:Seq X) n m:
      (forall z, z < m - n -> p (w (z + n))) ->
      forall k, n <=k <m -> p (w k).
  Proof.
    intros Z k.
    remember (k - n) as z.
    intros L.
    rewrite_eq (k = z + n).
    apply Z.
    omega.
  Qed.
  
  Context {A : finType}.
  Variables aut1 aut2: BuechiAut A.

  Inductive WaitFinal : Type :=
       |Wait1 : WaitFinal
       |Wait2 : WaitFinal
       |Final : WaitFinal.

  (** Showing that WaitFinal is a finite state is hidden *)
  Instance waitfinal_eq_dec: eq_dec WaitFinal.
  Proof.
    intros w w'. unfold dec. decide equality.
  Qed. 
  Canonical Structure EqWaitFinal := EqType WaitFinal.

  Lemma waitfinal_enum_ok x: count (cons Wait1 (cons Wait2 (cons Final nil))) x =1.
  Proof.
    destruct x;simpl; repeat destruct decision; try reflexivity; try discriminate; exfalso; tauto.
  Qed.

  Instance finTypeC_WaitFinal : finTypeC EqWaitFinal.
  Proof.
    econstructor. apply waitfinal_enum_ok.
  Defined.
  Canonical Structure finType_WaitFinal : finType := FinType EqWaitFinal.

  (** *** Definition of the intersection automaton *)
  Definition intersection_state :=  (state aut1) (x) (state aut2) (x) finType_WaitFinal.

  Definition intersection_transition (s1:intersection_state) a (s2:intersection_state) := match s1,s2 with
          | (s1, s2, w),(s1',s2', w') => 
             if (decision ( (transition (aut:=aut1) s1 a s1') /\ (transition (aut:=aut2) s2 a s2')))
                then match w,w' with
                   | Wait1, Wait1 => ~(final_state s1')
                   | Wait1, Wait2 => final_state s1'
                   | Wait2, Wait2 => ~(final_state s2')
                   | Wait2, Final =>  final_state s2'
                   | Final, Wait1 =>  True
                   | _, _ => False
                end
             else False
       end.

  Definition intersection_initial (s:intersection_state) := match s with
         | (s1, s2, Wait1) => (initial_state s1) /\ (initial_state s2)
         | _ => False
  end.

  (** We define the final states to be the ones where we visit a state marked Final *)
  Definition intersection_final (s:intersection_state) := snd s =  Final.

  Lemma intersection_transition_dec s a s': dec (intersection_transition s a s').
  Proof.
      destruct s as [[s1 s2] [| |]]; destruct s' as [[s1' s2'] [| |]]; simpl;
      decide ((transition s1 a s1') /\ (transition s2 a s2')); auto.
  Qed.
    
  Lemma intersection_initial_dec s: dec (intersection_initial s).
  Proof.
    destruct s as [[s1 s2] [| |]]; auto.
  Qed.
    
  Lemma intersection_final_dec s: dec(intersection_final s).
  Proof.
     destruct s as [[s1 s2] [| |]]; auto.
  Qed.

  Definition autI:= mknfa intersection_transition_dec intersection_initial_dec intersection_final_dec.

  (** *** Show that given an accepting run of both automata, the intersection automaton accepts the sequence too. *)
  Definition project_first (r: Run autI): (Run aut1) := fun n => (fst (fst (r n))).
  Definition project_second(r: Run autI): (Run aut2) := fun n => (snd (fst (r n))).

  Lemma project_first_is_valid w r: valid_run (aut:=autI) r w -> valid_run (aut:=aut1) (project_first r) w.
  Proof.
    intros V n. unfold project_first.
    destruct (r n) as [[s1 s2] z] eqn:H. destruct (r (S n)) as [[s1' s2'] z'] eqn:H'.
    specialize (V n).
    rewrite H, H' in V.  simpl in V.
    decide (transition s1 (w n) s1' /\ transition s2 (w n) s2') as [[B _] |B]; tauto.
  Qed.

  Lemma project_second_is_valid w r: valid_run (aut:=autI) r w -> valid_run (aut:=aut2) (project_second r) w.
  Proof.
    intros V n. unfold project_second.
    destruct (r n) as [[s1 s2] z] eqn:H. destruct (r (S n)) as [[s1' s2'] z'] eqn:H'.
    specialize (V n).
    rewrite H, H' in V. simpl in V.
    decide (transition s1 (w n) s1' /\ transition s2 (w n) s2') as [[_ B] |B]; tauto.
  Qed.

  (** **** aut1 accepts all sequences accepted by intersection_aut
      To show that there are infinitely many final states for aut1, we need to find a final state
      of aut1 between two final states of the intersection automaton
      The recursive functions searches backwards starting at index l and returns the index
      of a final state where the flag changed (or zero, if none found) *)

  Fixpoint find_final_aut1 (r: Run autI) l := match l with
       | 0 => 0
       | S l' => match r l' with
          | (s1, s2, Wait1) => match r l with
             | (s1', s2', Wait2) => l
             | _ => find_final_aut1 r l'
            end  
          | _ => find_final_aut1 r l'
          end
       end.

  Lemma find_final_aut1_less r l: find_final_aut1 r l<= l.
  Proof.
    induction l; simpl.
    - omega.
    - destruct (r (S l)) as [[s1 s2] [| |]]; destruct (r l) as [[s1' s2'] [| |]];  omega.
  Qed.

  (** If there are two positions in the accepting run where one is Wait1 and the bigger is Wait2, then there is final state of aut1 in between *)
  Lemma find_final_aut1_correct r w  l n: valid_run (aut:=autI)  r w -> l > n -> snd (r n) = Wait1 -> snd (r (l)) = Wait2 ->
         (find_final_aut1 r l >= S n /\ final_state (fst (fst (r (find_final_aut1 r l))))).
  Proof.
    intros V L W1 W2.
    remember (l - (S n)) as d. assert (l = d + S n) as Z by omega.
    subst l. clear L. clear Heqd.
    induction d; simpl.
    - simpl. destruct (r (n)) as [[s1 s2] [| |]] eqn:Hn.
      + destruct (r (S n)) as [[s1' s2'] [| |]] eqn:HSn; simpl in *.
        * rewrite HSn in W2.  discriminate W2.
        * split; oauto.
          specialize (V n).
          rewrite Hn, HSn in V. simpl in V.
          decide (transition s1 (w n) s1' /\transition s2 (w n) s2'); try tauto.
          now rewrite HSn.
        * rewrite HSn in W2.  discriminate W2.
      + discriminate W1.
      + discriminate W1.
    - destruct (r (d + (S n))) as [[s1 s2] [| |]] eqn:Hn.
      + destruct (r (S (d + S n))) as [[s1' s2'] [| |]] eqn:HSn.  
        * rewrite_eq ((S (d + S n) = S d + S n)) in HSn. rewrite HSn in W2. discriminate W2.
        * split; oauto.
          specialize (V (d + S n)).
          rewrite Hn, HSn in V. simpl in V.
          decide  (transition s1 (w (d + S n)) s1' /\ transition s2 (w (d + S n)) s2'); try tauto.
          now rewrite HSn.
        * rewrite_eq (S (d + S n) = S d + S n) in HSn. rewrite HSn in W2. discriminate W2.
      + auto.
      + exfalso.
        specialize (V (d + S n)).
        destruct (r (S (d + S n))) as [[s1' s2'] z'] eqn:HSn.
        rewrite_eq (S d + S n = (S (d + S n))) in W2.
        rewrite HSn in W2. simpl in W2.
        rewrite Hn, W2 in V. simpl in V.
        decide (transition s1 (w (d + S n)) s1' /\ transition s2 (w (d + S n))  s2'); contradiction V.
  Qed. 
  

  Lemma stateAfterFinalIsWait1 w r n: valid_run (aut:=autI) r w -> final_state (r n) -> snd (r (S n)) = Wait1.
  Proof.
    intros V F.
    specialize (V n). simpl in V.
    destruct (r n) as [[s1 s2] z]; destruct (r (S n)) as [[s1' s2'] z'].
    simpl in F. rewrite F in V. simpl in V.
    destruct z'; decide (transition s1 (w n) s1' /\ transition s2 (w n) s2'); tauto.
  Qed.

  Lemma stateBeforeFinalIsWait2 w r n: valid_run (aut:=autI) r w -> final_state (r (S n)) -> snd (r n) = Wait2.
  Proof.
    intros V F.
    specialize (V n); simpl in V.
    destruct (r n) as [[s1 s2] z]; destruct (r (S n)) as [[s1' s2'] z'].
    simpl in F. rewrite F in V. simpl in V.
    destruct z; decide ((transition s1 (w n) s1' /\transition s2 (w n) s2')); tauto.
  Qed.
    
  Lemma there_is_aut1_final_in_between w r n m s: valid_run (aut:= autI) r w ->
       S (S n) < m -> final_state  s -> r n = s -> r m = s -> Sigma k, n <= k <= m /\ final_state  (fst (fst (r k))) .
  Proof.
    intros V L F En Em.
    assert (snd (r (S n)) = Wait1) as H. { apply (stateAfterFinalIsWait1 V). now rewrite En. }
    destruct m. { exfalso. omega. } 
    assert (snd (r m) = Wait2) as H2. { apply (stateBeforeFinalIsWait2 V). now rewrite Em. }
    exists (find_final_aut1 r m).
    pose (find_final_aut1_less r m).
    destruct (find_final_aut1_correct (l := m) (n := S n) V) as [P1 P2]; repeat(split); oauto.
  Qed.

  Lemma there_are_infinite_final_aut1 w r s: valid_run(aut:=autI) r w -> final_state s -> infinite s r
      -> forall n, exists m, m >= n /\ final_state (fst (fst (r m))) .
  Proof.
    intros V F I n.
    destruct (I n) as [m1 [Pm1 Qm1]].
    destruct (I (S (S(S m1)))) as [m2 [Pm2 Qm2]].
    assert( S(S m1) < m2) as H by omega.
    destruct (there_is_aut1_final_in_between V H F) as [m [Pm Qm]]; auto.
    exists m. split; oauto.
  Qed.
      
  Lemma autI_incl_aut1 : L_B autI <$= L_B aut1 .
  Proof.
    intros w [r [V [I [s [Inf Fin]]]]].
    exists (project_first r). repeat split.
    - now apply project_first_is_valid.
    - unfold initial, project_first in *.
      destruct (r 0) as [[s0 ?] [| |]]; simpl in I; tauto.
    - pose (P := (project_first_is_valid V)).
      apply (infinite_final_is_accepting_for_finite_automaton (aut:= aut1)).
      unfold project_first.
      destruct s as [[s1 s2] [| |]] eqn:H.
      + discriminate Fin.
      + discriminate Fin.
      + apply (there_are_infinite_final_aut1 V Fin Inf).
  Qed.

  (** **** aut2 acceepts all sequences accepted by intersection_aut *)

  Lemma final_state_intersection_is_final_state_aut2 r w s1 s2 n: valid_run (aut:=autI) r w -> initial r -> r n = (s1,s2, Final)
         -> final_state s2.
  Proof.
    intros V I E.
    destruct n.
    - exfalso. unfold initial in I. rewrite E in I. now simpl in I.
    - specialize (V n).
      rewrite E in V.
      destruct (r n) as [[s1' s2'] z']. simpl in V.
      decide ((transition s1' (w n) s1) /\ (transition s2' (w n) s2)); destruct z'; tauto.
  Qed.  
       
  Lemma autI_incl_aut2: L_B autI <$= L_B aut2.
  Proof.
    intros w [r [V [I [s [Inf Fin]]]]].
    exists (project_second r). repeat split.
    - now apply project_second_is_valid.
    - unfold initial, project_second in *.
      destruct (r 0) as [[? s0] [| |]]; simpl in *; tauto.
    - pose (P := (project_second_is_valid V)).
      apply (infinite_final_is_accepting_for_finite_automaton (aut:= aut2)).
      unfold project_second.
      destruct s as [[s1 s2] [| |]] eqn:H.
      + discriminate Fin.
      + discriminate Fin.
      + intros n.
        destruct (Inf n) as [m [Pm Qm]].
        exists m. split.
        * omega.
        * rewrite Qm.  simpl. apply (final_state_intersection_is_final_state_aut2 V I Qm).
  Qed.

  (** *** intersection_aut accepts all sequences accepted by aut1 and aut 2
     We need to compute the run of the intersection automaton according to its transition relation *)
  Fixpoint intersection_run (r1: Run aut1) (r2: Run aut2) (n:nat) : (state autI) :=
       match n with
       | 0 => (r1 0, r2 0, Wait1)
       | S n' => match (intersection_run r1 r2 n') with
           | (s1, s2, Wait1) => if (decision (final_state (r1 n)))
                                  then (r1 n, r2 n, Wait2)
                                  else (r1 n, r2 n, Wait1)
           | (s1, s2, Wait2) => if (decision (final_state (r2 n)))
                                  then (r1 n, r2 n, Final)
                                  else (r1 n, r2 n, Wait2)
           | (s1, s2, Final) => (r1 n, r2 n, Wait1)
                  end
       end.

  Lemma intersection_run_does_not_change_states r1 r2: forall n, let r := intersection_run r1 r2 in
         (fst (fst (r n))) = r1 n /\ (snd (fst (r n))) = r2 n.
  Proof.
    intros n r. unfold r. destruct n.
    - simpl. tauto.
    - simpl. destruct (intersection_run r1 r2 n) as [[s1 s2] [| |]]; repeat destruct decision; simpl; tauto.
  Qed.

  Lemma intersection_run_is_valid r1 r2 w: valid_run r1 w -> valid_run r2 w -> valid_run (intersection_run r1 r2) w.
  Proof.
    intros V1 V2 n. simpl.
    specialize (V1 n). specialize (V2 n).
    destruct (intersection_run r1 r2 n) as [[s1 s2] z]  eqn:H.
    assert(s1 = r1 n /\ s2 = r2 n) as [H1 H2]. { pose (P:=(intersection_run_does_not_change_states r1 r2 n)). simpl in P. now rewrite H in P. } 
    rewrite <-H1 in V1. rewrite <-H2 in V2.
    destruct z; simpl; repeat destruct decision; auto.
  Qed. 

  Lemma intersectionRunStaysWait1UntilNextFinalAut1 r1 r2 w n k:
       (valid_run r1 w) -> 
       S n <= k -> snd (intersection_run r1 r2 n) = Wait1 ->
       (forall m' : nat, S n <= m' < k -> ~ final_state (r1 m')) ->
       final_state (r1 k) ->
       (forall m, n <= m < k -> snd (intersection_run r1 r2 m) = Wait1).
  Proof.
    intros V1 Pm' E P3 P2. 
    apply (leq_to_distance (w:= intersection_run r1 r2) (p:=fun q => snd q = Wait1)).
    induction z; intros L; simpl.
    - auto.
    - destruct (intersection_run r1 r2 (z + n)) as [[s1' s2']z'] eqn:Hz.
      simpl in IHz.
      rewrite IHz by omega. 
      decide (final_state (r1 (S (z + n)))) as[D|D].
      + exfalso. apply (P3 (S (z + n))); oauto.
      + now reflexivity.
  Qed.

  Lemma intersectionRunStaysWait2UntilNextFinalAut2 r1 r2 w n k:
       (valid_run r2 w) -> 
       S n <= k -> snd (intersection_run r1 r2 n) = Wait2 ->
       (forall m' : nat, S n <= m' < k -> ~ final_state (r2 m')) ->
       final_state (r2 k) ->
       (forall m, n <= m < k -> snd (intersection_run r1 r2 m) = Wait2).
  Proof.
    intros V2 Pm' E P3 P2. 
    apply (leq_to_distance (w:= intersection_run r1 r2) (p:=fun q => snd q = Wait2)).
    induction z; intros L; simpl.
    - auto.
    - destruct (intersection_run r1 r2 (z + n)) as [[s1' s2']z'] eqn:Hz.
      simpl in IHz.
      rewrite IHz by omega. 
      decide (final_state (r2 (S (z + n)))) as[D|D].
      + exfalso. apply (P3 (S (z + n))); oauto.
      + now reflexivity.
  Qed.
    
  Lemma intersectionRunSwitchtesFromWait1ToWait2 r1 r2 n w: 
       (valid_run r1 w) -> (valid_run r2 w) ->
       (final r1) ->
       snd (intersection_run r1 r2 n) = Wait1 ->
        exists m, m >= n /\ snd (intersection_run r1 r2 m) = Wait2.
  Proof.
    intros V1 V2[f1 [Inf1 Fin1]] E.
    destruct (Inf1 (S (S n))) as [m [Pm Qm]].
    assert (S n <= m) as Pm' by omega.
    rewrite <-Qm in Fin1.
    destruct (can_find_next_position (final_state_dec (A:=A)(aut:=aut1) ) Pm' Fin1) as [k [P1 [P2 P3]]].
    exists k. split; oauto.
    destruct k as [|k].
    - exfalso. omega.
    - destruct (intersection_run r1 r2 k) as [[s1k s2k] zk] eqn:Hk.
      simpl. rewrite Hk.
      assert (zk = Wait1) . {
        enough (snd(intersection_run r1 r2 k ) = Wait1) as H0.
        - rewrite Hk in H0. exact H0.
        - apply intersectionRunStaysWait1UntilNextFinalAut1  with (n:=n) (k:=(S k)) (w:=w); oauto. }
      subst zk.
      decide ((final_state (r1 (S k)))); tauto.
  Qed.

  Lemma intersectionRunSwitchtesFromWait2ToFinal r1 r2 n w: 
       (valid_run r1 w) -> (valid_run r2 w) ->
       (final r2) ->
       snd (intersection_run r1 r2 n) = Wait2 ->
        exists m, m >= n /\ snd (intersection_run r1 r2 m) = Final.
  Proof.
    intros V1 V2[f1 [Inf1 Fin1]] E.
    destruct (Inf1 (S (S n))) as [m [Pm Qm]].
    assert (S n <= m) as Pm' by omega.
    rewrite <-Qm in Fin1.
    destruct (can_find_next_position (final_state_dec (A:=A)(aut:=aut2) ) Pm' Fin1) as [k [P1 [P2 P3]]].
    exists k. split; oauto.
    destruct k as [|k].
    - exfalso. omega.
    - destruct (intersection_run r1 r2 k) as [[s1k s2k] zk] eqn:Hk.
      simpl. rewrite Hk.
      assert (zk = Wait2) . {
        enough (snd(intersection_run r1 r2 k ) = Wait2) as H0.
        - rewrite Hk in H0. exact H0.
        - apply intersectionRunStaysWait2UntilNextFinalAut2  with (n:=n) (k:=(S k)) (w:=w); oauto. }
      subst zk.
      decide ((final_state (r2 (S k)))); tauto.
  Qed.

  Lemma aut1_inter_aut2_incl_autI: L_B aut1 /$\ L_B aut2 <$= L_B autI.
  Proof.
    intros w [[r1 [V1 [I1 fin1]]] [r2 [V2 [I2 fin2]]]].
    exists (intersection_run r1 r2). repeat split.
    - apply (intersection_run_is_valid V1 V2).
    - apply I1.
    - apply I2.
    - apply (infinite_final_is_accepting_for_finite_automaton (aut:= autI)).
      intros n.
      destruct (intersection_run r1 r2 n) as [[s1' s2'] [| |]] eqn:Hn; simpl; unfold intersection_final.
      + destruct (intersectionRunSwitchtesFromWait1ToWait2 (n:=n) V1 V2 fin1) as [m [Q1 Q2]].
        * now rewrite Hn.  
        * destruct (intersectionRunSwitchtesFromWait2ToFinal (n:= m) V1 V2 fin2 Q2) as [m' [P1 P2]].
          exists m'. split; oauto.
      + apply (intersectionRunSwitchtesFromWait2ToFinal (n:=n) V1 V2 fin2). now rewrite Hn.
      + exists n. split.
        * omega.
        * now rewrite Hn.
  Qed.

  Lemma closed_intersection: Sigma autI, L_B autI =$= L_B aut1 /$\ L_B aut2.
  Proof.
    exists autI. intros w. split.
    - intros WI. auto using autI_incl_aut1, autI_incl_aut2.
    - intros [W1 W2]. auto using aut1_inter_aut2_incl_autI.
  Qed.

  Definition intersect:= projT1 closed_intersection.
  
  Lemma intersect_correct: L_B intersect =$= L_B aut1 /$\ L_B aut2.
  Proof.
    unfold intersect. now destruct closed_intersection.
  Qed.

End Closed_Intersection.