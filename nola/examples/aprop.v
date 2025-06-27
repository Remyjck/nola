From nola.iris Require Import cif inv sinv.
From nola.iris Require Export inv_deriv.
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
    ∀ (P : (JUDG -n> iProp Σ) -> iProp Σ) (P_cif : cif CON Σ),
      (∀ δ, ⟦ P_cif ⟧ᶜ(δ) ∗-∗ P δ) ->
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
  Definition aProp_to_iProp_deriv δ {b} (P: aProp b) :=
  match P with
  | IProp P => P
  | FProp P _ _ => P δ
  end.

  Program Definition IProp_to_FProp {b} (P : aProp b) : aProp false :=
    match P with
    | IProp P => FProp (λ _, ▷ P)%I (▷ P)%cif _
    | FProp iP P HP => FProp iP P HP
    end.

  Coercion aProp_to_bi_car {b} (P : aProp b) : bi_car (iProp Σ) :=
    match P with
    | IProp P => P
    | FProp iP P HP => iP der
    end.

  Program Definition nola_to_FML (P : aProp false) : cif CON Σ.
  Proof.
    dependent destruction P.
    apply P_cif.
  Defined.

  Lemma sm_to_FML (P : aProp false) : ⟦ nola_to_FML P ⟧ᶜ ≡ aProp_to_iProp_deriv der P.
  Proof.
    dependent destruction P; cbn.
    iSplit; by [ iPoseProof (b der) as "[Himp _]" |iPoseProof (b der) as "[_ Himp]" ].
  Qed.

  Coercion aProp_to_FML {b} : aProp b -> cif CON Σ :=
    nola_to_FML ∘ IProp_to_FProp.

  Coercion aProp_to_ofe_car {b} (P : aProp b) : ofe_car (cif CON Σ)
    := aProp_to_FML P.

  Definition ofe_car_iprop := ofe_car (iProp Σ).
  Coercion aProp_to_ofe_car' {b} (P : aProp b) : ofe_car_iprop
    := aProp_to_iProp_deriv der P.

  Definition ofe_car_ofunc {CON Σ} := ofe_car (oFunctor_apply (cifOF CON) (iProp Σ)).
  Coercion aProp_to_ofe_car_func {b} (P : aProp b) : ofe_car_ofunc
    := aProp_to_FML P.

End embedding.

Arguments aProp _ _ _ {_} _.

Notation "↑⟦ P ⟧" := (aProp_to_iProp_deriv der P).
Notation "↑⟦ P ⟧( δ )" := (aProp_to_iProp_deriv δ P).

Section connectives.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Local Notation "'aProp'" := (aProp CON JUDG Σ).

  Program Definition aProp_sep {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) : aProp (b₁ || b₂) :=
    match P, Q with
    | IProp P, IProp Q => IProp (P ∗ Q)%I
    | IProp P, FProp Q _ _ => IProp (P ∗ Q der)%I
    | FProp P _ _, IProp Q => IProp (P der ∗ Q)%I
    | FProp iP P HP, FProp iQ Q HQ =>
        FProp (λ δ, iP δ ∗ iQ δ)%I (P ∗ Q)%cif _
    end.
  Next Obligation.
    clear Heq_P Heq_Q.
    specialize (HP δ); specialize (HQ δ).
    iSplit;
      by (iIntros "[HP HQ]";
       iSplitL "HP";
       [ iApply HP | iApply HQ ]).
  Defined.

  Program Definition aProp_all {A : Type@{cif_all.u0}} {b : bool} (P : A -> aProp b) : aProp b.
  Proof.
    destruct b.
    - constructor.
      refine (∀ a, ↑⟦ P a ⟧)%I.
    - eapply (FProp (λ δ, ∀ a, ↑⟦ P a ⟧(δ))%I (∀ a, aProp_to_FML (P a))%cif).
      intros δ. simpl.
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
    - eapply (FProp (λ δ, ∃ a, ↑⟦ P a ⟧(δ))%I (∃ a, aProp_to_FML (P a))%cif).
      intros δ; simpl.
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
    | IProp P, FProp Q _ _ => IProp (P -∗ Q der)%I
    | FProp P _ _, IProp Q => IProp (P der -∗ Q)%I
    | FProp iP P HP, FProp iQ Q HQ =>
        FProp (λ δ, iP δ -∗ iQ δ)%I (P -∗ Q)%cif _
    end.
  Next Obligation.
    clear Heq_P Heq_Q.
    specialize (HP δ); specialize (HQ δ).
    iSplit; iIntros "HP→Q HP"; iApply HQ; iApply "HP→Q".
    - iPoseProof HP as "[_ HiP→P]"; by iApply "HiP→P".
    - iPoseProof HP as "[HP→iP _]"; by iApply "HP→iP".
  Defined.

  Program Definition aProp_pure (P : Prop) : aProp false :=
    FProp (λ _, ⌜P⌝%I) (cif_pure P) _.

End connectives.

Infix "∗" := aProp_sep : aprop_scope.
Notation "∀ x .. y , Px" :=
  (aProp_all (λ x, .. (aProp_all (λ y, Px%a)) ..)) : aprop_scope.
Notation "∃ x .. y , Px" :=
  (aProp_ex (λ x, .. (aProp_ex (λ y, Px%a)) ..)) : aprop_scope.
Infix "-∗" := aProp_wand : aprop_scope.
Notation "⌜ φ ⌝" := (aProp_pure φ) : aprop_scope.

From nola.examples Require Import con deriv.

Section inv.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ), !lrustGS_gen hlc Σ,
    !inv'GS (cifOF CON) Σ, !invC CON, !iffJ (cifO CON Σ) JUDG,
    !invCS CON JUDG Σ, !iffJS (cifOF CON) JUDG Σ}.

  Set Printing Coercions.

  Local Notation "'aProp'" := (aProp CON JUDG Σ).

  Program Definition ainv_tok {b} N (P : aProp b) : aProp false :=
    FProp (λ δ, inv' δ N P) (cif_inv N P) _.
  Next Obligation.
    unfold aProp_to_ofe_car, aProp_to_FML; simpl.
    setoid_rewrite sem_cif_in; simpl.
    iIntros; iApply bi.wand_iff_refl.
  Defined.
  Arguments ainv_tok {_} _ _%_aprop_scope.

  (** Allocate [inv_tok] suspending the world satisfaction *)
  Lemma inv'_tok_alloc_suspend {sm} Px N :
    inv_wsat sm ==∗ invd N Px ∗ (sm Px -∗ inv_wsat sm).
  Proof.
    rewrite /inv' inv.inv_wsat_unseal. iIntros "W".
    iDestruct (sinv_tok_alloc_suspend Px with "W") as (I) "big".
    iMod (alloc_ownD I N) as (???) "D". iMod ("big" with "[//]") as "[#i →W]".
    iModIntro. iSplitR.
    { iExists Px. rewrite inv.inv_tok_unseal. iFrame "i %".
      iApply Deriv_factor; iIntros.
      rewrite in_js. cbn. unfold iffJT_sem. iModIntro.
      iSplit; by iIntros. }
    iIntros "HP". iApply "→W". unfold inv.inv_sem. iLeft. iFrame.
  Qed.
  (** Allocate [inv_tok] *)
  Lemma inv'_tok_alloc {sm} Px N : sm Px =[inv_wsat sm]=∗ invd N Px.
  Proof.
    iIntros "? W". iMod (inv'_tok_alloc_suspend with "W") as "[$ →W]". iModIntro.
    by iApply "→W".
  Qed.

  Definition invariant_unfold {b} (P : aProp b) := IProp_to_FProp P.

  Lemma ainv_tok_alloc {b} N (P : aProp b) :
    P -∗ bupdw (inv_wsat ⟦⟧ᶜ) (ainv_tok N P).
  Proof.
    iIntros "HP W".
    unfold ainv_tok. simpl.
    iMod ( @inv'_alloc CON JUDG Σ Csem0 Jsem0 hlc _ _ _ _ _ _ der_Deriv with "[HP] W") as "[W Hinv]".
    { instantiate (1 := P).
      dependent destruction P; cbn.
      - iApply "HP".
      - by iApply b. }
    iFrame "W".
    iApply "Hinv".
  Qed.

  Lemma ainv_tok_inv_alloc {b} N1 N2 (P : aProp b) : N1 ## N2 ->
    P -∗ bupdw (inv_wsat ⟦⟧ᶜ) (ainv_tok N2 (ainv_tok N1 P)).
  Proof.
    iIntros (Hmasks) "HP W".
    iMod (ainv_tok_alloc with "HP W") as "[W #Hinv]".
    iMod (ainv_tok_alloc with "Hinv W") as "[W #Hinvinv]".
    iModIntro. iFrame.
    iApply "Hinvinv".
  Qed.

  Lemma ainv_tok_acc {N E b} {Px : aProp b} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      (invariant_unfold Px) ∗ (invariant_unfold Px =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    simpl.
    rewrite /inv' inv.inv_wsat_unseal => NE. iIntros "[%Q #[HJ sm]] W".
    iDestruct (der_sound with "HJ") as "{HJ}HJ"; rewrite in_js /= /iffJT_sem.
    rewrite inv.inv_tok_unseal; iDestruct "sm" as "(%i & %iN & sm)".
    iMod (inv.fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct (sinv_tok_acc with "sm W") as "[in →W]".
    iDestruct "in" as "[[HP D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as %[]. }
    iDestruct ("→W" with "[$i]") as "$". iIntros "!>".
    iSplitL "HP".
    { dependent destruction Px; cbn.
      - by iApply "HJ".
      - iApply b. by iApply "HJ". }
    iIntros "Px W".
    iDestruct (sinv_tok_acc with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as %[]. }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
    dependent destruction Px; cbn.
    - iApply ("HJ" with "Px").
    - iApply "HJ". by iApply b.
  Qed.

  Lemma ainv_tok_acc_nola {N E} {Px : aProp false} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      Px ∗ (Px =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (Hmask) "HP".
    iPoseProof (ainv_tok_acc with "HP") as "Hinv". eassumption.
    dependent destruction Px; simpl. iApply "Hinv".
  Qed.

  Lemma ainv_tok_acc_iprop {N E} {Px : aProp true} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      ▷ Px ∗ (▷ Px =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (Hmask) "HP".
    iPoseProof (ainv_tok_acc with "HP") as "Hinv". eassumption.
    dependent destruction Px; simpl. iApply "Hinv".
  Qed.

  Lemma ainv_tok_acc_2 {N1 N2 E} {P : aProp false} : N1 ## N2 -> ↑N2 ⊆ E -> ↑N1 ⊆ E →
    ainv_tok N2 (ainv_tok N1 P) =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N2∖↑N1}=∗
      invariant_unfold P ∗ (invariant_unfold P =[inv_wsat ⟦⟧ᶜ]{E∖↑N2∖↑N1,E}=∗ True).
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

  Lemma inv_iff' {N : namespace} `{!Deriv ih δ} {Px Qx : cif CON Σ} :
    □ (∀ δ, ⌜Deriv ih δ⌝ -∗ ⟦ Px ⟧(δ) ∗-∗ ⟦ Qx ⟧(δ)) -∗
    inv' δ N Px -∗ inv' δ N Qx.
  Proof.
    iIntros "#Hequiv".
    iApply inv'_iff.
    iModIntro. iIntros.
    by iApply "Hequiv".
  Qed.

  Lemma inv_iff {N : namespace} `{!Deriv ih δ} {Px Qx : cif CON Σ} :
    □ (∀ δ, ⌜Deriv ih δ⌝ -∗ ⟦ Px ⟧(δ) ∗-∗ ⟦ Qx ⟧(δ)) -∗
    inv' δ N Px ∗-∗ inv' δ N Qx.
  Proof.
    iIntros "#Hequiv".
    iSplit; iApply inv_iff'; iIntros "!> %δ' %Hderiv". by iApply "Hequiv".
    iApply util.wand_iff_comm. by iApply "Hequiv".
  Qed.

  Lemma semantic_alteration' {b} N (P Q : aProp b) :
    □ (∀ δ ih, ⌜Deriv ih δ⌝ -∗ ↑⟦ P ⟧(δ) ∗-∗ ↑⟦ Q ⟧(δ)) -∗
    ainv_tok N P -∗ ainv_tok N Q.
  Proof.
    iIntros "#Hequiv".
    unfold ainv_tok; cbn.
    iIntros "Hinv".
    iApply (inv'_iff with "[] Hinv").
    iIntros "!>" (δ' HDeriv _ Hsound).
    unfold aProp_to_ofe_car.
    destruct b; dependent destruction P; dependent destruction Q; cbn.
    - iSplit; iIntros; iNext; by iApply ("Hequiv" $! der _ der_Deriv).
    - iSplit; cbn; iIntros "HP".
      + iApply b0. iApply ("Hequiv" $! δ' _ HDeriv). by iApply b.
      + iApply b. iApply ("Hequiv" $! δ' _ HDeriv). by iApply b0.
  Qed.

  Lemma semantic_alteration {b} N (P Q : aProp b) :
    □ (∀ δ ih, ⌜Deriv ih δ⌝ -∗ ↑⟦ P ⟧(δ) ∗-∗ ↑⟦ Q ⟧(δ)) -∗
    ainv_tok N P ∗-∗ ainv_tok N Q.
  Proof.
    iIntros "#Hequiv".
    iSplit; iApply semantic_alteration'; iIntros "!> %δ %ih %Hder"; [ | iApply util.wand_iff_comm ];
    iApply ("Hequiv" $! _ _ Hder).
  Qed.

  Lemma commute_under_inv {b₁ b₂} N₁ N₂ (P : aProp b₁) (Q : aProp b₂) :
    ainv_tok N₁ (ainv_tok N₂ (P ∗ Q)) ∗-∗ ainv_tok N₁ (ainv_tok N₂ (Q ∗ P)).
  Proof.
    iApply semantic_alteration; iIntros "!> %δ %ih %Hder".
    simpl.
    iApply inv_iff; iIntros "%δ' %Hder' !>".
    dependent destruction P; dependent destruction Q; cbn;
    rewrite bi.sep_comm;
    iApply bi.wand_iff_refl.
  Qed.

End inv.
