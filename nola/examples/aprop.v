From nola.iris Require Import cif inv sinv.
From nola.util Require Import tagged.
From iris.base_logic.lib Require Export wsat invariants.
From iris.proofmode Require Import proofmode.
From nola.examples Require Export con.

From Stdlib Require Import Program.

Import ProeqvNotation FunPRNotation iPropAppNotation ModwNotation DsemNotation CsemNotation.

Section embedding.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.

  Inductive aProp : bool -> Type :=
  | IProp :
    ∀ (P : iProp Σ), aProp true
  | FProp :
    ∀ (P : iProp Σ) (P_cif : cif CON Σ),
      cif_sem der P_cif ≡ P ->
      aProp false.

  Definition nola_prop := aProp false.
  Definition iris_prop := aProp true.
  #[reversible] Coercion aProp_to_iProp {b} (P: aProp b) :=
  match P with
  | IProp P => P
  | FProp P _ _ => P
  end.

  Program Definition aProp_sep {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) : aProp (b₁ || b₂) :=
    match P, Q with
    | IProp P, IProp Q | IProp P, FProp Q _ _ | FProp P _ _, IProp Q =>
        IProp (P ∗ Q)%I
    | FProp iP P HP, FProp iQ Q HQ =>
        FProp (iP ∗ iQ)%I (P ∗ Q)%cif _
    end.
  Next Obligation. rewrite HP. rewrite HQ. reflexivity. Defined.


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

  Coercion aProp_to_FML {b} : aProp b -> cif CON Σ :=
    nola_to_FML ∘ IProp_to_FProp.

  Coercion aProp_to_ofe_car {b} (P : aProp b) : ofe_car (cif CON Σ)
    := aProp_to_FML P.

  Definition ofe_car_iprop := ofe_car (iProp Σ).
  Coercion aProp_to_ofe_car' {b} (P : aProp b) : ofe_car_iprop
    := aProp_to_iProp P.

  Definition ofe_car_ofunc {CON Σ} := ofe_car (oFunctor_apply (cifOF CON) (iProp Σ)).
  Coercion aProp_to_ofe_car_func {b} (P : aProp b) : ofe_car_ofunc
    := aProp_to_FML P.

  Lemma sm_to_FML (P : aProp false) : cif_sem der P ≡ (aProp_to_iProp P).
  Proof. by dependent destruction P. Qed.


  Program Definition aProp_all {A : Type@{cif_all.u0}} {b : bool} (P : A -> aProp b) : aProp b.
  Proof.
    destruct b.
    - constructor.
      refine (∀ a, (P a))%I.
    - eapply (FProp (∀ a, aProp_to_iProp (P a))%I (∀ a, aProp_to_FML (P a))%cif).
      simpl. apply bi.forall_proper.
      apply pointwise_pointwise.
      split. remember (P y) as Q; dependent destruction Q; subst; rewrite <- HeqQ.
      by destruct e.
  Defined.

  Program Definition aProp_all_pred {A : Type@{universes.Quant}} (P : A -> ∀ b, aProp b) : aProp true.
  Proof.
    constructor.
    refine (∀ a, aProp_to_iProp (P a true))%I.
  Defined.

  Program Definition aProp_ex {A : Type@{cif_ex.u0}} {b : bool} (P : A -> aProp b) : aProp b.
  Proof.
    destruct b.
    - constructor.
      refine (∃ a, aProp_to_iProp (P a))%I.
    - eapply (FProp (∃ a, aProp_to_iProp (P a))%I (∃ a, aProp_to_FML (P a))%cif).
      simpl. apply bi.exist_proper.
      apply pointwise_pointwise.
      split. remember (P y) as Q; dependent destruction Q; subst; rewrite <- HeqQ.
      by destruct e.
  Defined.

  Program Definition aProp_ex_pred {A : Type@{universes.Quant}} (P : A -> ∀ b, aProp b) : aProp true.
  Proof.
    constructor.
    refine (∃ a, aProp_to_iProp (P a true))%I.
  Defined.

  Program Definition aProp_wand {b₁ b₂ : bool} (P : aProp b₁) (Q : aProp b₂) : aProp (b₁ || b₂) :=
    match P in aProp b₁, Q in aProp b₂ with
    | IProp P, IProp Q | IProp P, FProp Q _ _ | FProp P _ _, IProp Q =>
        IProp (P -∗ Q)%I
    | FProp iP P HP, FProp iQ Q HQ =>
        FProp (iP -∗ iQ)%I (P -∗ Q)%cif _
    end.
  Next Obligation. rewrite HP. rewrite HQ. reflexivity. Defined.

End embedding.

Arguments aProp _ _ _ {_ _}.

Section inv.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ),
            !invGS_gen hlc Σ,
            !inv'GS (cifOF CON) Σ, !inv_tokC CON, !inv_tokCS CON JUDG Σ}.

  Set Printing Coercions.

  Program Definition ainv_tok {b} N (P : aProp CON JUDG Σ b) : aProp CON JUDG Σ false :=
    FProp (inv_tok N P) (cif_inv_tok N P) _.
  Next Obligation.
    unfold aProp_to_ofe_car, aProp_to_FML; simpl.
    rewrite sem_cif_in; simpl. reflexivity.
  Defined.

  Definition invariant_unfold {b} (P : aProp CON JUDG Σ b) := IProp_to_FProp P.

  Lemma ainv_tok_alloc {b} N (P : aProp CON JUDG Σ b) :
    P -∗ bupdw (inv_wsat ⟦⟧ᶜ) (ainv_tok N P).
  Proof.
    iIntros "HP W".
    iApply (inv.inv_tok_alloc with "[HP] W").
    dependent destruction P; simpl.
    - by iNext.
    - by rewrite e.
  Qed.

  Lemma ainv_tok_inv_alloc {b} N1 N2 (P : aProp CON JUDG Σ b) : N1 ## N2 ->
    P -∗ bupdw (inv_wsat ⟦⟧ᶜ) (ainv_tok N2 (ainv_tok N1 P)).
  Proof.
    iIntros (Hmasks) "HP W".
    iMod (ainv_tok_alloc with "HP W") as "[W #Hinv]".
    iMod (ainv_tok_alloc with "Hinv W") as "[W #Hinvinv]".
    iModIntro. iFrame.
    iApply "Hinvinv".
  Qed.

  Lemma ainv_tok_acc {N E b} {Px : aProp CON JUDG Σ b} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      (invariant_unfold Px) ∗ (invariant_unfold Px =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    simpl.
    rewrite inv.inv_tok_unseal inv.inv_wsat_unseal=> NE. iIntros "[%i[%iN #sm]] W".
    iMod (inv.fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct (sinv_tok_acc with "sm W") as "[in →W]".
    iDestruct "in" as "[[HP D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as %[]. }
    iDestruct ("→W" with "[$i]") as "$". iIntros "!>".
    iSplitL "HP".
    { dependent destruction Px; simpl.
      - iApply "HP".
      - by rewrite e. }
    iIntros "Px W".
    iDestruct (sinv_tok_acc with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as %[]. }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
    dependent destruction Px; simpl.
    - iApply "Px".
    - by rewrite e.
  Qed.

  Lemma ainv_tok_acc_nola {N E} {Px : aProp CON JUDG Σ false} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      Px ∗ (Px =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (Hmask) "HP".
    iPoseProof (ainv_tok_acc with "HP") as "Hinv". eassumption.
    dependent destruction Px; simpl. iApply "Hinv".
  Qed.

  Lemma ainv_tok_acc_iprop {N E} {Px : aProp CON JUDG Σ true} : ↑N ⊆ E →
    ainv_tok N Px =[inv_wsat ⟦⟧ᶜ]{E,E∖↑N}=∗
      ▷ Px ∗ (▷ Px =[inv_wsat ⟦⟧ᶜ]{E∖↑N,E}=∗ True).
  Proof.
    iIntros (Hmask) "HP".
    iPoseProof (ainv_tok_acc with "HP") as "Hinv". eassumption.
    dependent destruction Px; simpl. iApply "Hinv".
  Qed.

  Lemma ainv_tok_acc_2 {N1 N2 E} {P : aProp CON JUDG Σ false} : N1 ## N2 -> ↑N2 ⊆ E -> ↑N1 ⊆ E →
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

End inv.
