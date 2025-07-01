From nola.examples Require Import aprop con.
From nola.bi Require Import wpw.
From nola.lrust Require Import proofmode.

Section awp.

  Context `{!Csem CON JUDG Σ, Jsem JUDG (iProp Σ)}.
  Context `{!lrustGS_gen hlc Σ}.
  Context `{!inv'GS (cifOF CON) Σ}.

  Local Notation "'aProp'" := (aProp CON JUDG Σ).

  Definition awp b s E e (Φ : _ -> aProp b) := wpw (inv_wsat (cif_sem der)) s E e%E (λ v, aProp_to_iProp_deriv der (Φ v)).
  Definition atwp b s E e (Φ : _ -> aProp b) := twpw (inv_wsat (cif_sem der)) s E e%E (λ v, aProp_to_iProp_deriv der (Φ v)).


  Lemma atwp_awp {b} s E e (Φ : _ -> aProp b) :
    atwp b s E e Φ ⊢ awp b s E e Φ.
  Proof.
    apply twpw_wpw.
  Qed.

End awp.

Section custom_wp.

  Context `{!Csem CON JUDG Σ, Jsem JUDG (iProp Σ)}.
  Context `{!lrustGS_gen hlc Σ}.
  Context `{!inv'GS (cifOF CON) Σ}.

  (** ** Custom constructors *)

  (** [customCT]: Constructor *)
  Variant customCT_id := .
  Variant customCT_sel :=
  | (** WP token *) cifs_wp (b : bool) (s : stuckness) (E : coPset) (e : language.expr lrust_lang) (Φ : language.val lrust_lang → aProp CON JUDG Σ b)
  | (** Total WP token *) cifs_twp (b : bool) (s : stuckness) (E : coPset) (e : language.expr lrust_lang) (Φ : language.val lrust_lang → aProp CON JUDG Σ b).
  Arguments cifs_wp {_}.
  Arguments cifs_twp {_}.

  Definition customCT := Cifcon customCT_id (customCT_sel)
  (λ _, Empty_set) (λ _, Empty_set) (λ _, unitO) _.
  (** [customC]: [customCT] registered *)
  (*
      [inC : cifcon → cifcon → Type]
      To be understood as the inclusion of one custom constructor
      structure for [cif] into another.
  *)
  Notation customC := (inC customCT).
  Section customC.
    Context `{!customC CON}.
    (** [cif_wp]: WP token *)
    Definition cif_wp {b} s E e Φ : cif CON Σ :=
      cif_in customCT ( @cifs_wp b s E e Φ) nullary nullary ().
    (** [cif_twp]: TWP token *)
    Definition cif_twp {b} s E e Φ : cif CON Σ :=
      cif_in customCT ( @cifs_twp b s E e Φ) nullary nullary ().

    (** Semantics of [customCT] *)
    Definition customCT_sem (s : customCT_sel) : iProp Σ :=
      match s with
      | @cifs_wp b s E e Φ => awp b s E e Φ
      | @cifs_twp b s E e Φ => atwp b s E e Φ
      end.
    #[export] Program Instance customCT_ecsem
      : Ecsem customCT CON JUDG Σ :=
      ECSEM (λ _ _ s _ _ _, customCT_sem s) _.
    Next Obligation (* Proof of non-expansiveness *). done. Qed.
  End customC.
  (** [customC] semantics registered *)

  Notation customCS := (inCS customCT).

  Section customC.
    Context `{!customC CON, !customCS CON JUDG Σ}.

    (** Reify token *)
    #[export] Program Instance wp_as_cif {b} s E e Φ :
        AsCif CON (λ _, awp b s E e Φ)%I := AS_CIF (cif_wp s E e Φ) _.
    Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
    #[export] Program Instance twp_as_cif {b} s E e Φ :
        AsCif CON (λ _, atwp b s E e Φ)%I := AS_CIF (cif_twp s E e Φ) _.
    Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
  End customC.

End custom_wp.

Section aProp_wp.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Context `{!lrustGS_gen hlc Σ}.
  Context `{!inv'GS (cifOF CON) Σ}.
  Context `{!inC customCT CON, !inCS customCT CON JUDG Σ}.
  Local Notation aProp b := (aProp CON JUDG Σ b).

  Program Definition aProp_wp {b} s E e Φ: aProp false :=
    FProp (λ _, awp b s E e Φ) (cif_wp s E e Φ) _.
  Next Obligation. intros b s E e Φ δ. rewrite sem_cif_in /=. apply bi.wand_iff_refl. Defined.

  Program Definition aProp_twp {b} s E e Φ : aProp false :=
    FProp (λ _, atwp b s E e Φ) (cif_twp s E e Φ) _.
  Next Obligation. intros b s E e Φ δ. rewrite sem_cif_in /=. apply bi.wand_iff_refl. Defined.

End aProp_wp.

From Stdlib Require Import Program.

Section awp.
  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Context `{!lrustGS_gen hlc Σ}.
  Context `{!inv'GS (cifOF CON) Σ}.
  Context `{!inC customCT CON, !inCS customCT CON JUDG Σ}.

  Lemma twp_wp {b} s E e (Φ : _ -> aProp CON JUDG Σ b) :
    ⊢ (aProp_twp s E e Φ -∗ aProp_wp s E e Φ)%a.
  Proof.
    cbn.
    iIntros "Htwp". iApply (twpw_wpw with "Htwp").
  Qed.

  Lemma wand_sound {b1 b2} (P : aProp CON JUDG Σ b1) (Q : aProp CON JUDG Σ b2) :
    (P -∗ Q)%I ∗-∗
    (P -∗ Q)%a.
  Proof.
    dependent destruction P; dependent destruction Q; cbn; iApply bi.wand_iff_refl.
  Qed.

  Lemma wp_sound {b} s E e (Φ : _ -> aProp CON JUDG Σ b) :
    wpw (inv_wsat (cif_sem der)) s E e (λ v, aProp_to_iProp_deriv der (Φ v)) ∗-∗ aProp_wp s E e Φ.
  Proof.
    cbn; unfold awp. apply bi.wand_iff_refl.
  Qed.

End awp.