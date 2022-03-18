Require Import Classical.
(* Used only in deciding whether a pair is derivable or not. *)

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.

Require Import Ensembles.
Require Import Prop_Bi_Int_calcs.
Require Import Prop_Bi_Int_logics.
Require Import Prop_Bi_Int_extens_interactions.
Require Import Prop_wBi_Int_meta_interactions.
Require Import Prop_sBi_Int_meta_interactions.
Require Import Prop_Bi_Int_Kripke_sem.
Require Import Prop_Bi_Int_bisimulation.
Require Import Prop_Bi_Int_Lindenbaum_lem.
Require Import Prop_Bi_Int_wcompleteness.

Fixpoint n_reachable {W : Type} (R : W -> W -> Prop) (n: nat) (w v : W) : Prop :=
  match n with
  | 0 => w = v
  | S m => exists u, ((R u v) \/ (R v u)) /\ (n_reachable R m w u)
  end.

Lemma DN_form_DN : forall n A, (DN_form (S n) A) = (DN_form n (Neg (wNeg A))).
Proof.
induction n.
- intros. simpl. auto.
- intros. simpl. pose (IHn A). rewrite <- e. simpl. auto.
Qed.

Definition s_C_is_n_reachable (s cp : Canon_worlds) : Prop :=
  exists n, @n_reachable Canon_worlds Canon_relation n s cp.

Lemma n_reachable_DN_clos : forall W R R_props val pers n w A,
  (wforces W R R_props val pers w (DN_form n A)) ->
    (forall v, (n_reachable R n w v) -> (wforces W R R_props val pers v A)).
Proof.
intros W R R_props val pers. induction n.
- intros. simpl in H. inversion H0. subst. auto.
- intros. inversion H0. destruct H1. destruct H1.
  * pose (IHn w (Neg (wNeg A))). pose (DN_form_DN n A). rewrite e in H.
    pose (w0 H x H2). simpl in w1. pose (w1 v H1).
    destruct (wforces_dec A W R R_props val pers v) ; auto. exfalso.
    apply f. exists v. split ; auto. destruct R_props. apply r.
  * pose (IHn w (Neg (wNeg A))). pose (DN_form_DN n A). rewrite e in H.
    pose (w0 H x H2). simpl in w1. pose (w1 x).
    destruct (wforces_dec A W R R_props val pers v) ; auto. exfalso.
    apply f. destruct R_props. apply r. exists v. split ; auto.
Qed.

Lemma DN_clos_DN_form : forall n Γ A, (In (BPropF V) Γ A) -> (In (BPropF V) (DN_clos_set Γ) (DN_form n A)).
Proof.
induction n.
- intros. simpl. apply InitClo. auto.
- intros. simpl. apply IndClo. apply IHn. auto.
Qed.

Definition s_pruned_Canon_worlds (s : Canon_worlds) : Type :=
  { x : Canon_worlds | s_C_is_n_reachable s x}.

Definition s_pruned_Canon_relation (s : Canon_worlds) (cp0 cp1 : s_pruned_Canon_worlds s) : Prop :=
  Canon_relation (proj1_sig cp0) (proj1_sig cp1).

Lemma s_C_R_refl (s : Canon_worlds) : R_refl (s_pruned_Canon_relation s).
Proof.
unfold R_refl. intros. unfold s_pruned_Canon_relation.
intro. intros. assumption.
Qed.

Lemma s_C_R_trans (s : Canon_worlds) : R_trans (s_pruned_Canon_relation s).
Proof.
unfold R_trans. intros. unfold s_pruned_Canon_relation.
intro. intros. unfold Canon_relation in H0. unfold Canon_relation in H.
apply H0. apply H. auto.
Qed.

Lemma s_C_R_props (s : Canon_worlds) : (R_refl (s_pruned_Canon_relation s) * R_trans (s_pruned_Canon_relation s)).
Proof.
split. apply s_C_R_refl. apply s_C_R_trans.
Qed.

Definition s_pruned_Canon_valuation (s : Canon_worlds) (cp : s_pruned_Canon_worlds s) (q : V) : Prop :=
  Canon_valuation (proj1_sig cp) q.

Lemma s_C_val_persist (s : Canon_worlds) :
  val_persist_R _ (s_pruned_Canon_valuation s) (s_pruned_Canon_relation s).
Proof.
unfold val_persist_R. intros.
unfold s_pruned_Canon_valuation in H0. unfold s_pruned_Canon_relation in H.
unfold s_pruned_Canon_valuation. apply H. auto.
Qed.

Theorem sCounterCompleteness : forall (Γ Δ : @Ensemble (BPropF V)),
    (spair_derrec (Γ, Δ) -> False) -> ((glob_conseq Γ Δ) -> False).
Proof.
intros Γ Δ SD.
assert (J1: spair_derrec (DN_clos_set Γ, Δ) -> False).
intro. apply SD. unfold spair_derrec in H. unfold spair_derrec.
destruct H. destruct H. destruct H0. simpl in H0.
simpl in H1. exists x. repeat split ; auto. simpl.
pose (sBIC_comp _ H1 Γ). simpl in s. apply s. clear s. intros.
induction H2. apply Ids. apply IdRule_I. assumption.
apply DNs with (ps:=[(Γ, A)]). intros. inversion H3. subst. auto.
inversion H4. apply DNsRule_I.
assert (J2: wpair_derrec (DN_clos_set Γ, Δ) -> False).
intro. apply J1. apply pair_sBIC_extens_wBIC ; auto.
apply Lindenbaum_lemma in J2. destruct J2. destruct H.
destruct H. destruct H0. destruct H1.
assert (J3: CompNotDer (x,x0)). unfold CompNotDer. auto.
pose (@exist (prod (Ensemble (BPropF V)) (Ensemble (BPropF V))) CompNotDer (x,x0) J3).
assert (J4: s_C_is_n_reachable s s). unfold s_C_is_n_reachable. exists 0. simpl. auto.
pose (@exist Canon_worlds (s_C_is_n_reachable s) s J4).

assert (Bisim: forall (cp : (s_pruned_Canon_worlds s)),
  bisimulation Canon_worlds Canon_relation C_R_props Canon_valuation C_val_persist
  (s_pruned_Canon_worlds s) (s_pruned_Canon_relation s) (s_C_R_props s) (s_pruned_Canon_valuation s)
  (s_C_val_persist s) (fun (x : Canon_worlds) (y : (s_pruned_Canon_worlds s)) => x = (proj1_sig y))).
{ intros. unfold bisimulation. intros. subst. repeat split.
  - intro. unfold s_pruned_Canon_valuation. auto.
  - intro. unfold s_pruned_Canon_valuation. auto.
  - intros. exists (proj1_sig v1). split ; auto.
  - intros. assert (J20: s_C_is_n_reachable s v0).
    unfold s_C_is_n_reachable. destruct w1. simpl in H3. unfold s_C_is_n_reachable in s1.
    destruct s1. exists (S x2). simpl. exists x1. auto.
    pose (@exist Canon_worlds (s_C_is_n_reachable s) v0 J20). exists s1.
    auto.
  - intros. exists (proj1_sig v1). split ; auto.
  - intros. assert (J20: s_C_is_n_reachable s v0).
    unfold s_C_is_n_reachable. destruct w1. simpl in H3. unfold s_C_is_n_reachable in s1.
    destruct s1. exists (S x2). simpl. exists x1. auto.
    pose (@exist Canon_worlds (s_C_is_n_reachable s) v0 J20). exists s1.
    auto. }

(* All formulae in Γ are globally true in the pruned canonical model. *)
assert (SAT: forall (cp : (s_pruned_Canon_worlds s)) A, (In _ Γ A) ->
wforces (s_pruned_Canon_worlds s) (s_pruned_Canon_relation s) (s_C_R_props s)
(s_pruned_Canon_valuation s) (s_C_val_persist s) cp A).
{ intros. pose (bisimulation_imp_bi_int_equiv _ _ _ _ _ _ _ _ _ _ _ (Bisim cp)).
  pose (i A (proj1_sig cp) cp). apply i0. auto. clear i0. clear i. destruct cp. simpl.
  unfold s_C_is_n_reachable in s1. destruct s1.
  assert (J5: wforces Canon_worlds Canon_relation C_R_props Canon_valuation C_val_persist s (DN_form x2 A)).
  { apply truth_lemma. simpl. apply H. apply DN_clos_DN_form. auto. }
  pose (n_reachable_DN_clos Canon_worlds Canon_relation C_R_props Canon_valuation
  C_val_persist x2 s A J5 x1). auto. }

(* No formula in Δ is satisfied in s0 in the pruned canonical model. *)
assert (NotSAT: forall A, (In _ Δ A) ->
((wforces (s_pruned_Canon_worlds s) (s_pruned_Canon_relation s) (s_C_R_props s)
(s_pruned_Canon_valuation s) (s_C_val_persist s) s0 A) -> False)).
{ intros. pose (bisimulation_imp_bi_int_equiv _ _ _ _ _ _ _ _ _ _ _ (Bisim s0)).
  pose (i A (proj1_sig s0) s0). apply i0 in H4. clear i0. clear i. clear Bisim.
  apply truth_lemma in H4. simpl in H4. apply H2. exists [A].
  repeat split. apply NoDup_cons ; auto ; apply NoDup_nil. intros.
  inversion H5. simpl. subst. apply H0. auto. inversion H6. simpl.
  apply MP with (ps:=[(x, Imp A (Or A (Bot V)));(x, A)]). 2: apply MPRule_I.
  intros. inversion H5. subst. apply Ax. apply AxRule_I. apply RA2_I.
  exists A. exists (Bot V). auto. inversion H6. subst. 2: inversion H7.
  apply Id. apply IdRule_I. auto. auto. }

intro. unfold glob_conseq in H3. clear Bisim.
assert (J6: (forall A : BPropF V, In (BPropF V) Γ A -> mforces (s_pruned_Canon_worlds s)
(s_pruned_Canon_relation s) (s_C_R_props s) (s_pruned_Canon_valuation s) (s_C_val_persist s) A)).
{ intros. unfold mforces. intros. apply SAT ; auto. }

pose (H3 (s_pruned_Canon_worlds s) (s_pruned_Canon_relation s) (s_C_R_props s)
(s_pruned_Canon_valuation s) (s_C_val_persist s) J6 s0). destruct e.
destruct H4. apply NotSAT with (A:=x1) ; auto.
Qed.

Theorem sCompleteness : forall (Γ Δ : @Ensemble (BPropF V)),
    (glob_conseq Γ Δ) -> spair_derrec (Γ, Δ).
Proof.
intros Γ Δ GC. pose (sCounterCompleteness Γ Δ).
pose (classic (spair_derrec (Γ, Δ))). destruct o. auto. exfalso.
apply f ; assumption.
Qed.
