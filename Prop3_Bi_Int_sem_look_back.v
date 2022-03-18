Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Prop3_Bi_Int_calcs.
Require Import Prop3_Bi_Int_logics.
Require Import Prop3_Bi_Int_extens_interactions.
Require Import Prop3_wBi_Int_meta_interactions.
Require Import Prop3_sBi_Int_meta_interactions.
Require Import Prop3_Bi_Int_Kripke_sem.
Require Import Prop3_Bi_Int_soundness.
Require Import Prop3_Bi_Int_wcompleteness.
Require Import Prop3_Bi_Int_scompleteness.

Variable q : V.
Variable p : V.
Hypothesis diff_prop : (p = q) -> False.

(* sBIC is not included in wBIC. *)

Lemma wBIC_not_der_p_DNp : forall (p : V),
  (wpair_derrec (Singleton _ (# p), Singleton _ (Neg (wNeg (# p))))) -> False.
Proof.
intros p wpair. apply wSoundness in wpair. unfold loc_conseq in wpair.
assert (J1: R_refl (fun x y => ((x = 0) /\ (y = 1)) \/ (x = y)) * R_trans (fun x y => ((x = 0) /\ (y = 1)) \/ (x = y))).
{ simpl. split.
  - unfold R_refl. intro ; auto.
  - unfold R_trans. intros. destruct H ; destruct H0. destruct H ; destruct H0 ; auto.
    subst ; auto. subst ; auto. subst ; auto. }
assert (J2: val_persist_R nat (fun (n : nat) (_ : V) => 1 <= n) (fun x y : nat => (x = 0) /\ (y = 1) \/ (x = y))).
{ unfold val_persist_R. intros. destruct H. destruct H. subst. auto. subst. auto. }
assert (J3: (forall A : BPropF V, In _ (Singleton _ (# p)) A ->
wforces nat (fun x y : nat => (x = 0) /\ (y = 1) \/ (x = y)) J1 (fun (n : nat) (_ : V) => 1 <= n) J2 1 A)).
{ intros. inversion H. subst. simpl. auto. }
pose (@wpair nat (fun x y => ((x = 0) /\ (y = 1)) \/ (x = y)) J1
(fun n p => 1 <= n) J2 1 J3).
destruct e. destruct H. inversion H. subst. simpl in H0.
assert (J4: (1 = 0) /\ (1 = 1) \/ (1 = 1)). auto.
pose (@H0 1 J4). apply f. exists 0. split. auto. split ; auto. intro. lia.
Qed.

Theorem sBIC_not_incl_wBIC : exists G,
   (spair_derrec G) /\
   ((wpair_derrec G) -> False).
Proof.
exists ((Singleton _ (# p), Singleton _ (Neg (wNeg (# p))))).
split. 2 : apply wBIC_not_der_p_DNp. pose (extens_diff_sBIC p). unfold spair_derrec.
exists [Neg (wNeg # p)]. repeat split. apply NoDup_cons. intro. inversion H. apply NoDup_nil.
intros. simpl. inversion H. subst. apply In_singleton. inversion H0.
simpl.
apply MPs with (ps:=[(Singleton _ # p, Imp (Neg (wNeg # p)) (Or (Neg (wNeg # p)) (Bot V)));(Singleton _ # p, (Neg (wNeg # p)))]).
2: apply MPRule_I. intros. inversion H. subst. apply Axs. apply AxRule_I.
apply RA2_I. exists (Neg (wNeg # p)). exists (Bot V). auto. inversion H0.
subst. assumption. inversion H1.
Qed.

Theorem failure_gen_sBIC_Deduction_Theorem : exists A B Γ,
  (spair_derrec (Union _ Γ (Singleton _ (A)), Singleton _ (B))) /\
  ((spair_derrec (Γ, Singleton _ (A → B))) -> False).
Proof.
exists (# p). exists (Neg (wNeg (# p))). exists (Empty_set _).
split.
- unfold spair_derrec. exists [(Neg (wNeg (# p)))].
  repeat split. apply NoDup_cons. intro. inversion H. apply NoDup_nil.
  intros. simpl. inversion H. subst. apply In_singleton. inversion H0.
  simpl. assert (Union _ (Empty_set _) (Singleton _ # p) = Singleton _ # p).
  apply Extensionality_Ensembles. unfold Same_set. split. intro. intros.
  inversion H. inversion H0. inversion H0. subst ; auto. intro. intros.
  inversion H. subst. apply Union_intror. auto. rewrite H. pose (extens_diff_sBIC p).
  apply MPs with (ps:=[(Singleton _ # p, Imp (Neg (wNeg # p)) (Or (Neg (wNeg # p)) (Bot V)));(Singleton _ # p, (Neg (wNeg # p)))]).
  2: apply MPRule_I. intros. inversion H0. subst. apply Axs. apply AxRule_I.
  apply RA2_I. exists (Neg (wNeg # p)). exists (Bot V). auto. inversion H1. subst.
  assumption. inversion H2.
- intro. apply sSoundness in H. unfold glob_conseq in H.
  assert (J1: R_refl (fun x y => ((x = 0) /\ (y = 1)) \/ (x = y)) * R_trans (fun x y => ((x = 0) /\ (y = 1)) \/ (x = y))).
  { simpl. split.
    - unfold R_refl. intro ; auto.
    - unfold R_trans. intros. destruct H0 ; destruct H1. destruct H0 ; destruct H1 ; auto.
      subst ; auto. subst ; auto. subst ; auto. }
  assert (J2: val_persist_R nat (fun (n : nat) (_ : V) => 1 <= n) (fun x y : nat => (x = 0) /\ (y = 1) \/ (x = y))).
  { unfold val_persist_R. intros. destruct H0. destruct H0. subst. auto. subst. auto. }
  assert (J3: (forall A : BPropF V, In _ (Empty_set _) A ->
  mforces nat (fun x y : nat => (x = 0) /\ (y = 1) \/ (x = y)) J1 (fun (n : nat) (_ : V) => 1 <= n) J2 A)).
  { intros. inversion H0. }
  pose (@H nat (fun x y => ((x = 0) /\ (y = 1)) \/ (x = y)) J1
  (fun n p => 1 <= n) J2 J3 1).
  destruct e. destruct H0. inversion H0. subst. simpl in H1.
  assert (J4: (1 = 0) /\ (1 = 1) \/ (1 = 1)). auto.
  assert (J5: 1 <= 1). auto.
  pose (@H1 1 J4 J5). apply f with (v:=1). auto. exists 0. split. auto. split ; auto. intro. lia.
Qed.

Theorem failure_gen_sBIC_Dual_Detachment_Theorem : exists A B Δ,
  (spair_derrec (Singleton _ (Excl A B), Δ)) /\
  ((spair_derrec (Singleton _ (A), Union _ (Singleton _ (B)) Δ)) -> False).
Proof.
exists (# p). exists (# q). exists (Singleton _ (Neg (wNeg (wNeg (# q))))). split.
- unfold spair_derrec. exists [(Neg (wNeg (wNeg (# q))))]. repeat split. apply NoDup_cons.
  intro. inversion H. apply NoDup_nil. intros. simpl. inversion H. subst. apply In_singleton.
  inversion H0. simpl.
  apply MPs with (ps:=[(Singleton _ (Excl # p # q), Imp (Neg (wNeg (wNeg # q))) (Or (Neg (wNeg (wNeg # q))) (Bot V)));(Singleton _ (Excl # p # q), (Neg (wNeg (wNeg # q))))]).
  2: apply MPRule_I. intros. inversion H. subst. apply Axs. apply AxRule_I.
  apply RA2_I. exists (Neg (wNeg (wNeg # q))). exists (Bot V). auto. inversion H0. subst.
  apply DNs with (ps:=[(Singleton _ (Excl # p # q), (wNeg # q))]). 2: apply DNsRule_I.
  intros. inversion H1. subst. apply sBIC_extens_wBIC.
  pose (wBIC_Detachment_Theorem (Empty_set _, Imp (Excl # p # q) (wNeg # q))). simpl in w.
  assert (Singleton _ (Excl # p # q) = Union _ (Empty_set _) (Singleton _ (Excl # p # q))).
  apply Extensionality_Ensembles. split. intro. intros. inversion H2. apply Union_intror. apply In_singleton.
  intro. intros. inversion H2. inversion H3. inversion H3. subst. apply In_singleton. rewrite H2. apply w ; try auto.
  apply wdual_residuation. pose (wBIC_Deduction_Theorem (Union _ (Empty_set _) (Singleton _ (# p)), Or # q (wNeg # q))).
  apply w0 ; auto. clear w0. clear w. pose (wBIC_monot (Empty_set _, Or # q (wNeg # q))). simpl in w.
  apply w. clear w.
  apply MP with (ps:=[(Empty_set _, Imp (Or # q (Excl (Top V) (# q))) (Or # q (wNeg # q)));(Empty_set _, Or # q (Excl (Top V) (# q)))]).
  2: apply MPRule_I. intros. inversion H3. subst.
  apply MP with (ps:=[(Empty_set _, ((Excl (Top V) # q) → Or # q (wNeg # q)) → (Or # q (Excl (Top V) # q) → Or # q (wNeg # q)));
  (Empty_set _, ((Excl (Top V) # q) → Or # q (wNeg # q)))]).
  2: apply MPRule_I. intros. inversion H4. subst.
  apply MP with (ps:=[(Empty_set _, (# q → Or # q (wNeg # q)) → ((Excl (Top V) # q) → Or # q (wNeg # q)) → (Or # q (Excl (Top V) # q) → Or # q (wNeg # q)));
  (Empty_set _, (# q) → Or # q (wNeg # q))]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA4_I.
  exists (# q). exists (Excl (Top V) # q). exists (Or # q (wNeg # q)). auto. inversion H6. subst.
  apply Ax. apply AxRule_I. apply RA2_I. exists (# q). exists (wNeg # q). auto. inversion H7. inversion H5. subst.
  apply MP with (ps:=[(Empty_set _, ((wNeg # q) → Or # q (wNeg # q)) → (Excl (Top V) # q → Or # q (wNeg # q)));(Empty_set _, ((wNeg # q) → Or # q (wNeg # q)))]).
  2: apply MPRule_I. intros. inversion H6. subst.
  apply MP with (ps:=[(Empty_set _,(Excl (Top V) # q → (wNeg # q)) → ((wNeg # q) → Or # q (wNeg # q)) → (Excl (Top V) # q → Or # q (wNeg # q)));
  (Empty_set _, (Excl (Top V) # q → (wNeg # q)))]).
  2: apply MPRule_I. intros. inversion H7. subst.
  apply Ax. apply AxRule_I. apply RA1_I. exists (Excl (Top V) # q). exists (wNeg # q).
  exists (Or # q (wNeg # q)). auto. inversion H8. subst. apply wimp_Id_gen. inversion H9.
  inversion H7. subst. apply Ax.
  apply AxRule_I. apply RA3_I. exists (# q). exists (wNeg # q). auto. inversion H8.
  inversion H6. inversion H4. subst.
  apply MP with (ps:=[(Empty_set _, Imp (Top V) (Or # q (Excl (Top V) # q)));(Empty_set _, Top V)]).
  2: apply MPRule_I. intros. inversion H5. subst. apply Ax. apply AxRule_I.
  apply RA11_I. exists (Top V). exists (# q). auto. inversion H6. subst.
  apply MP with (ps:=[(Empty_set _, Imp (Imp (Top V) (Top V)) (Top V));(Empty_set _, (Imp (Top V) (Top V)))]).
  2: apply MPRule_I. intros. inversion H7. subst. apply Ax. apply AxRule_I. apply RA15_I. exists (Top V → Top V). auto.
  inversion H8. subst. apply wimp_Id_gen. inversion H9. inversion H7. inversion H5.
  intro. intros. inversion H3. inversion H2. inversion H1.
- intro. apply sSoundness in H. unfold glob_conseq in H. Inductive Three := u | w | v.
  assert (J1: R_refl (fun x y : Three => (x = v) /\ (y = w) \/ (x = u) /\ (y = w) \/ (x = y)) *
  R_trans (fun x y : Three => (x = v) /\ (y = w) \/ (x = u) /\ (y = w) \/ (x = y))).
  { simpl. split.
    * unfold R_refl. intro. auto.
    * unfold R_trans. intros. destruct H0. destruct H0. subst. destruct H1. destruct H0. subst. auto. destruct H0.
      destruct H0. subst. auto. subst. auto. destruct H0. destruct H0. destruct H1. destruct H1. subst. auto.
      destruct H1. destruct H1. subst. auto. subst. auto. destruct H1. destruct H1. subst. auto. destruct H1.
      destruct H1. subst. auto. subst. auto. }
  assert (J2: val_persist_R Three (fun (x : Three) (r : V) =>  (x = x) /\ (r = p) \/ ((x = w) \/ (x = v)) /\ (r = q))
  (fun x y : Three => (x = v) /\ (y = w) \/ (x = u) /\ (y = w) \/ (x = y))).
  { intro. intros. destruct H0. destruct H0. subst. destruct H1. destruct H0. subst. auto. destruct H0.
    destruct H0. subst. auto. subst. auto. destruct H0. destruct H0. destruct H1. destruct H1. subst. auto.
    destruct H1. destruct H1. subst. auto. subst. auto. destruct H1. destruct H1. subst. auto. destruct H1.
    destruct H1. subst. auto. subst. auto. }
  assert (J3: (forall A : BPropF V, In _ (Singleton _ # p) A ->  mforces Three (fun x y : Three => (x = v) /\ (y = w) \/ (x = u) /\ (y = w) \/ (x = y))
  J1 (fun (x : Three) (r : V) => (x = x) /\ (r = p) \/ ((x = w) \/ (x = v)) /\ (r = q)) J2 A)).
  { intros. inversion H0. subst. intro. simpl. auto. }
  pose (H Three (fun x y => ((x = v) /\ (y = w)) \/ ((x = u) /\ (y = w)) \/ (x = y)) J1
  (fun x r => ((x = x) /\ (r = p)) \/ (((x = w) \/ (x = v)) /\ (r = q))) J2 J3 u). destruct e.
  destruct H0. inversion H0. inversion H2. subst. simpl in H1. destruct H1. destruct H1. inversion H3. 
  subst. apply diff_prop. auto. destruct H1. destruct H1. inversion H1. inversion H1. subst.
  clear H0. inversion H2. subst. simpl in H1. clear H2.
  assert (J4: (u = v) /\ (w = w) \/ (u = u) /\ (w = w) \/ (u = w)). auto.
  pose (H1 w J4). apply f. exists v. split. auto. split ; auto. intro. destruct H0. destruct H0. destruct H0.
  destruct H0. subst. inversion H3. destruct H0. destruct H0. inversion H3. subst.
  apply H2. auto.
Qed.








