From nola.iris Require Import cif inv sinv.
From nola.bi Require Import deriv.
From nola.util Require Import tagged.
From iris.base_logic.lib Require Export wsat invariants.
From iris.proofmode Require Import proofmode.

From Stdlib Require Import Program.

Import ProeqvNotation FunPRNotation iPropAppNotation ModwNotation DsemNotation CsemNotation.

Declare Scope aprop_scope.
Delimit Scope aprop_scope with a.

Section embedding.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  Inductive aProp : bool -> Type :=
  | IProp :
    ∀ (P : iProp Σ), aProp true
  | FProp :
    ∀ (P : iProp Σ) (P_cif : cif CON Σ),
      (⟦ P_cif ⟧ᶜ ∗-∗ P) ->
      aProp false.

  (** We need to parameterise [P] in [FProp P P_cif Hiff] because
      otherwise we cannot define our invariant token:

      [Program Definition ainv_tok {b} N (P : aProp b) : aProp false :=
        FProp_demo (invd N P) (cif_inv N P) _.]

      In order to complete the definition, we have to show
        ⊢ (∀ δ, ⟦ cif_inv N P ⟧ᶜ(δ) ∗-∗ invd N P)
      where [invd] := [inv' der], leading to an uprovable goal.

      Indeed, the correct definition is

      [Program Definition ainv_tok {b} N (P : aProp b) : aProp false :=
        FProp_demo (λ δ, inv' δ N P) (cif_inv N P) _.]

      For which the proof obligation is
        ⊢ (∀ δ, ⟦ cif_inv N P ⟧ᶜ(δ) ∗-∗ inv' δ N P),
      which holds.
  *)

  Definition nola_prop := aProp false.
  Definition iris_prop := aProp true.
  Definition aProp_to_iProp_deriv {b} (P: aProp b) :=
  match P with
  | IProp P => P
  | FProp P _ _ => P
  end.

  Program Definition IProp_to_FProp {b} (P : aProp b) : aProp false :=
    match P with
    | IProp P => FProp (▷ P)%I (▷ P)%cif _
    | FProp iP P HP => FProp iP P HP
    end.

  Coercion aProp_to_bi_car {b} (P : aProp b) : bi_car (iProp Σ) :=
    match P with
    | IProp P => P
    | FProp iP P HP => iP
    end.

  Program Definition nola_to_FML (P : aProp false) : cif CON Σ.
  Proof.
    dependent destruction P.
    apply P_cif.
  Defined.

  Lemma sm_to_FML (P : aProp false) : ⟦ nola_to_FML P ⟧ᶜ ≡ aProp_to_iProp_deriv P.
  Proof.
    dependent destruction P; cbn.
    iSplit; by [ iPoseProof b as "[Himp _]" |iPoseProof b as "[_ Himp]" ].
  Qed.

  Coercion aProp_to_FML {b} : aProp b -> cif CON Σ :=
    nola_to_FML ∘ IProp_to_FProp.

  Coercion aProp_to_ofe_car {b} (P : aProp b) : ofe_car (cif CON Σ)
    := aProp_to_FML P.

  Definition ofe_car_iprop := ofe_car (iProp Σ).
  Coercion aProp_to_ofe_car' {b} (P : aProp b) : ofe_car_iprop
    := aProp_to_iProp_deriv P.

  Definition ofe_car_ofunc {CON Σ} := ofe_car (oFunctor_apply (cifOF CON) (iProp Σ)).
  Coercion aProp_to_ofe_car_func {b} (P : aProp b) : ofe_car_ofunc
    := aProp_to_FML P.

End embedding.

Arguments aProp _ _ _ {_ _}.

Notation "↑⟦ P ⟧" := (aProp_to_iProp_deriv P).

Record NotDeriv `{!Csem CON JUDG Σ} `{!Jsem JUDG (iProp Σ)}
  {b} (p : aProp CON JUDG Σ b) := NOT_DERIV {
    not_deriv : match p with
    | IProp _ => True
    | FProp iP P HP =>
      ∃ Q, iP ∗-∗ Q
    end;
  }.

Existing Class NotDeriv.
Arguments NotDeriv {_ _ _ _ _ _} _. Arguments NOT_DERIV {_ _ _ _ _ _} _.

Section connectives.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Local Notation "'aProp'" := (aProp CON JUDG Σ).

  Definition aProp_equivalence {b₁ b₂} (P : aProp b₁) (Q : aProp b₂) : iProp Σ :=
    match P, Q with
    | IProp P, IProp Q => P ∗-∗ Q
    | IProp P, FProp iQ _ _ => ▷ P ∗-∗ iQ
    | FProp iP _ _, IProp Q => iP ∗-∗ ▷ Q
    | FProp iP _ _, FProp iQ _ _ => iP ∗-∗ iQ
    end.

  Program Definition aProp_sep {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) : aProp (b₁ || b₂) :=
    match P, Q with
    | IProp P, IProp Q => IProp (P ∗ Q)%I
    | IProp P, FProp Q _ _ => IProp (P ∗ Q)%I
    | FProp P _ _, IProp Q => IProp (P ∗ Q)%I
    | FProp iP P HP, FProp iQ Q HQ =>
        FProp (iP ∗ iQ)%I (P ∗ Q)%cif _
    end.
  Next Obligation.
    clear Heq_P Heq_Q.
    iSplit;
      by (iIntros "[HP HQ]";
       iSplitL "HP";
       [ iApply HP | iApply HQ ]).
  Defined.

  #[export] Instance notderiv_sep {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) `{!NotDeriv P, !NotDeriv Q}:
    NotDeriv (aProp_sep P Q).
  Proof.
    dependent destruction P; dependent destruction Q; cbn; try done.
    destruct NotDeriv0 as [[Qp HP]]. destruct NotDeriv1 as [[Qq HQ]].
    constructor. exists (Qp ∗ Qq)%I.
    iSplit; iIntros "[HP HQ]";
      (iSplitL "HP"; [ iApply HP; iApply "HP" | iApply HQ; iApply "HQ" ]).
  Qed.

  Program Definition aProp_all {A : Type@{cif_all.u0}} {b : bool} (P : A -> aProp b) : aProp b.
  Proof.
    destruct b.
    - constructor.
      refine (∀ a, ↑⟦ P a ⟧)%I.
    - eapply (FProp (∀ a, ↑⟦ P a ⟧)%I (∀ a, aProp_to_FML (P a))%cif).
      simpl.
      iSplit; iIntros "HP %a"; iSpecialize ("HP" $! a);
        remember (P a) as Q; dependent destruction Q; cbn;
        by iApply b.
  Defined.

  Program Definition aProp_all_pred {A : Type@{universes.Quant}} (P : A -> ∀ b, aProp b) : aProp true.
  Proof.
    constructor.
    refine (∀ a, ↑⟦ P a true ⟧)%I.
  Defined.

  Program Definition aProp_ex {A : Type@{cif_ex.u0}} {b : bool} (P : A -> aProp b) : aProp b.
  Proof.
    destruct b.
    - constructor.
      refine (∃ a, ↑⟦ P a ⟧)%I.
    - eapply (FProp (∃ a, ↑⟦ P a ⟧)%I (∃ a, aProp_to_FML (P a))%cif).
      simpl.
      iSplit; iIntros "[%a HP]"; iExists a;
        remember (P a) as Q; dependent destruction Q; cbn;
        by iApply b.
  Defined.

  Program Definition aProp_ex_pred {A : Type@{universes.Quant}} (P : A -> ∀ b, aProp b) : aProp true.
  Proof.
    constructor.
    refine (∃ a, ↑⟦ P a true ⟧)%I.
  Defined.

  Program Definition aProp_wand {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) : aProp (b₁ || b₂) :=
    match P, Q with
    | IProp P, IProp Q => IProp (P -∗ Q)%I
    | IProp P, FProp Q _ _ => IProp (P -∗ Q)%I
    | FProp P _ _, IProp Q => IProp (P -∗ Q)%I
    | FProp iP P HP, FProp iQ Q HQ =>
        FProp (iP -∗ iQ)%I (P -∗ Q)%cif _
    end.
  Next Obligation.
    clear Heq_P Heq_Q.
    iSplit; iIntros "HP→Q HP"; iApply HQ; iApply "HP→Q".
    - iPoseProof HP as "[_ HiP→P]"; by iApply "HiP→P".
    - iPoseProof HP as "[HP→iP _]"; by iApply "HP→iP".
  Defined.

  #[export] Instance notderiv_wand {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) `{!NotDeriv P, !NotDeriv Q} :
    NotDeriv (aProp_wand P Q).
  Proof.
    dependent destruction P; dependent destruction Q; cbn; try done.
    destruct NotDeriv0 as [[Qp HP]]. destruct NotDeriv1 as [[Qq HQ]].
    constructor. exists (Qp -∗ Qq)%I.
    iSplit; iIntros "Himp HP";
      iApply HQ; iApply "Himp"; iApply HP; iApply "HP".
  Qed.

  Program Definition aProp_pure (P : Prop) : aProp false :=
    FProp (⌜P⌝%I) (cif_pure P) _.

  #[export] Instance notderiv_pure P : NotDeriv (aProp_pure P).
  Proof.
    constructor;cbn.
    exists (⌜ P ⌝)%I.
    apply bi.wand_iff_refl.
  Qed.

End connectives.

Infix "∗" := aProp_sep : aprop_scope.
Notation "∀ x .. y , Px" :=
  (aProp_all (λ x, .. (aProp_all (λ y, Px%a)) ..)) : aprop_scope.
Notation "∃ x .. y , Px" :=
  (aProp_ex (λ x, .. (aProp_ex (λ y, Px%a)) ..)) : aprop_scope.
Infix "-∗" := aProp_wand : aprop_scope.
Notation "⌜ φ ⌝" := (aProp_pure φ) : aprop_scope.
Infix "≡" := aProp_equivalence : aprop_scope.

From nola.examples Require Import con deriv.

Section inv.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !lrustGS_gen hlc Σ,
    !inv'GS Σ, !inv_tokC CON, !inv_tokCS CON JUDG Σ}.

  Local Notation "'aProp'" := (aProp CON JUDG Σ).

  Program Definition ainv_tok {b} N (P : aProp b) : aProp false :=
    FProp (inv_tok N P) (cif_inv_tok N P) _.
  Next Obligation.
    unfold aProp_to_ofe_car, aProp_to_FML; simpl.
    setoid_rewrite sem_cif_in; simpl.
    iIntros; iApply bi.wand_iff_refl.
  Defined.
  Arguments ainv_tok {_} _ _%_aprop_scope.

  Definition invariant_unfold {b} (P : aProp b) := IProp_to_FProp P.

  Lemma ainv_tok_alloc {b} N (P : aProp b) :
    P -∗ bupdw (inv_wsat) (ainv_tok N P).
  Proof.
    iIntros "HP W".
    unfold ainv_tok. simpl.
    iMod (inv_tok_alloc with "[HP] W") as "[W Hinv]".
    { instantiate (1 := P).
      dependent destruction P; cbn.
      - iApply "HP".
      - by iApply b. }
    iFrame "W".
    iApply "Hinv".
  Qed.

  Lemma ainv_tok_inv_alloc {b} N1 N2 (P : aProp b) : N1 ## N2 ->
    P -∗ bupdw (inv_wsat) (ainv_tok N2 (ainv_tok N1 P)).
  Proof.
    iIntros (Hmasks) "HP W".
    iMod (ainv_tok_alloc with "HP W") as "[W #Hinv]".
    iMod (ainv_tok_alloc with "Hinv W") as "[W #Hinvinv]".
    iModIntro. iFrame.
    iApply "Hinvinv".
  Qed.

  Lemma ainv_tok_acc {N E b} {Px : aProp b} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat]{E,E∖↑N}=∗
      (invariant_unfold Px) ∗ (invariant_unfold Px =[inv_wsat]{E∖↑N,E}=∗ True).
  Proof.
    intros HNE.
    dependent destruction Px; cbn.
    - apply (inv.inv_tok_acc HNE (Px := ▷ P)).
    - iIntros "Hinv W".
      apply bi.wand_iff_equiv in b.
      rewrite <- b.
      iApply (inv.inv_tok_acc HNE with "Hinv W").
  Qed.

  Lemma ainv_tok_acc_nola {N E} {Px : aProp false} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat]{E,E∖↑N}=∗
      Px ∗ (Px =[inv_wsat]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (Hmask) "HP".
    iPoseProof (ainv_tok_acc with "HP") as "Hinv". eassumption.
    dependent destruction Px; simpl. iApply "Hinv".
  Qed.

  Lemma ainv_tok_acc_iprop {N E} {Px : aProp true} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat]{E,E∖↑N}=∗
      ▷ Px ∗ (▷ Px =[inv_wsat]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (Hmask) "HP".
    iPoseProof (ainv_tok_acc with "HP") as "Hinv". eassumption.
    dependent destruction Px; simpl. iApply "Hinv".
  Qed.

  Lemma ainv_tok_acc_2 {N1 N2 E} {P : aProp false} : N1 ## N2 -> ↑N2 ⊆ E -> ↑N1 ⊆ E →
    ainv_tok N2 (ainv_tok N1 P) =[inv_wsat]{E,E∖↑N2∖↑N1}=∗
      invariant_unfold P ∗ (invariant_unfold P =[inv_wsat]{E∖↑N2∖↑N1,E}=∗ True).
  Proof.
    simpl.
    iIntros (Hneq HN2 HN1) "Hinv W".
    iPoseProof (ainv_tok_acc with "Hinv W") as "Hinv". apply HN2.
    iMod "Hinv" as "(W & #Hinv & Hclose)".
    iPoseProof (ainv_tok_acc with "Hinv W") as "Hinv2". { instantiate (1 := E ∖ ↑N2). apply subseteq_difference_r; assumption. }
    iMod "Hinv2" as "(W & Hinv2 & Hclose2)".
    iModIntro. iFrame.
    iIntros "HP W".
    iDestruct ("Hclose2" with "HP W") as "Hmod".
    iMod "Hmod" as "[W _]".
    iSpecialize ("Hclose" with "Hinv W").
    iMod "Hclose".
    by iFrame.
  Qed.

  Lemma semantic_alteration_equiv' {b1 b2} N (P : aProp b1) (Q : aProp b2) :
    (⊢ (P ≡ Q)%a) ->
    ainv_tok N P -∗ ainv_tok N Q.
  Proof.
    unfold aProp_equivalence; intros Hequiv.
    unfold ainv_tok; cbn.
    iIntros "Hinv".
    dependent destruction P; dependent destruction Q; cbn in *;
      iApply (inv.sem_alteration with "Hinv"); cbn.
    - iSplit; iIntros; iNext; by iApply Hequiv.
    - iApply bi.wand_iff_trans. iSplitL; [iApply b | ].
      iApply bi.wand_iff_sym. iApply Hequiv.
    - iApply bi.wand_iff_trans. iSplitL; iApply bi.wand_iff_sym; [ | iApply b ].
      iApply Hequiv.
    - iApply bi.wand_iff_trans. iSplitL; [ iApply b0 | ].
      iApply bi.wand_iff_trans. iSplitL; iApply bi.wand_iff_sym; [ | iApply b ].
      iApply Hequiv.
  Qed.

  Lemma semantic_alteration_equiv {b1 b2} N (P : aProp b1) (Q : aProp b2) :
    (⊢ (P ≡ Q)%a) ->
    ainv_tok N P ∗-∗ ainv_tok N Q.
  Proof.
    intros Hequiv.
    iSplit; iApply semantic_alteration_equiv'.
    - apply Hequiv.
    - dependent destruction P; dependent destruction Q; cbn in *;
      iApply bi.wand_iff_sym; iApply Hequiv.
  Qed.

  Lemma semantic_alteration_equiv_equiv {b1 b2} N (P : aProp b1) (Q : aProp b2) :
    (⊢ (P ≡ Q)%a) ->
    ⊢ aProp_equivalence (ainv_tok N P) (ainv_tok N Q).
  Proof.
    intros Hequiv.
    destruct b2; dependent destruction P; dependent destruction Q;
      iApply semantic_alteration_equiv; apply Hequiv.
  Qed.

  Lemma exist_intro {A : Type} {b} {Ψ : A → aProp b} (a : A) : Ψ a ⊢ (∃ a0 : A, Ψ a0)%a.
  Proof.
    iIntros "HΨ".
    destruct b; cbn; iExists a;
      remember (Ψ a) as P;
      by dependent destruction P.
  Qed.

  Lemma aProp_equiv_sep_ex {A} {b} (P : A -> aProp b) (Q : A -> aProp b):
    (∀ a, (P a ≡ Q a)%a) -∗
    ((∃ a, P a) ≡ (∃ a, Q a))%a.
  Proof.
    iIntros "Hequiv".
    destruct b; cbn in *;
      iSplit; iIntros "[%a HP]"; iExists a;
      iSpecialize ("Hequiv" $! a);
      remember (P a) as Pa; remember (Q a) as Qa;
      dependent destruction Pa; dependent destruction Qa;
      by iApply "Hequiv".
  Qed.

  Lemma aProp_equiv_sep_comm {b₁ b₂} (P : aProp b₁) (Q : aProp b₂):
    ⊢ ((P ∗ Q)%a ≡ (Q ∗ P)%a)%a.
  Proof.
    dependent destruction P; dependent destruction Q; cbn;
    rewrite bi.sep_comm; iApply bi.wand_iff_refl.
  Qed.

  Lemma aProp_equiv_IProp (P Q : aProp true) :
    P ∗-∗ Q -∗
    (P ≡ Q)%a.
  Proof.
    iIntros "Hequiv";
    dependent destruction P; dependent destruction Q; cbn;
    iApply "Hequiv".
  Qed.

  Lemma commute_under_inv {b} N₁ N₂ (P : aProp b) (Q : aProp b) :
    ainv_tok N₁ (ainv_tok N₂ (P ∗ Q)) ∗-∗ ainv_tok N₁ (ainv_tok N₂ (Q ∗ P)).
  Proof.
    iApply semantic_alteration_equiv.
    iApply semantic_alteration_equiv_equiv.
    iApply aProp_equiv_sep_comm.
  Qed.

  Lemma modus_aponens {b1 b2} (P : aProp b1) (Q : aProp b2) :
    P -∗ (P -∗ Q)%a -∗ Q.
  Proof.
    iIntros "P Himp".
    dependent destruction P; dependent destruction Q; cbn;
    by iApply "Himp".
  Qed.

End inv.
