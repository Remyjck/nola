(** * Basics *)

From iris.proofmode Require Export environments.
From nola.util Require Export fn.
From nola.iris Require Export cif inv_deriv na_inv_deriv store_deriv
  pborrow_deriv fborrow.
From nola.examples Require Export xty.
From nola.lrust Require Export proofmode notation.
Export ProdNotation PlistNotation ProeqvNotation FunPRNotation BigSepPLNotation
  ModwNotation WpwNotation iPropAppNotation ProphNotation LftNotation
  CsemNotation XtyNotation.
Open Scope nat_scope.


Implicit Type Σ : gFunctors.

(** ** Ghost state *)

Class rust_haltGS CON Σ : Type := RustHaltGS {
rust_haltGS_lrust :: lrustGS_gen HasNoLc Σ;
rust_haltGS_inv :: inv'GS (cifOF CON) Σ;
rust_haltGS_na_inv :: na_invG Σ;
rust_haltGS_dinv :: dinvGS (cifOF CON) Σ;
rust_haltGS_token :: tokenG Σ;
rust_haltGS_borrow :: borrowGS (cifOF CON) Σ;
rust_haltGS_proph :: prophGS xty Σ;
rust_haltGS_proph_ag :: proph_agG nat xty Σ;
rust_haltGS_fborrow :: fborrowGS (cifOF CON) Σ;
}.

(** ** Custom constructors *)

(** [customCT]: Constructor *)
Variant customCT_id := .
Variant customCT_sel (A : cmra) :=
| (** Ownership token *) cifs_own (γ : gname) (a : cmra_car A).
Arguments cifs_own {_} _ _.
Set Printing Universes.


Definition customCT A := Cifcon customCT_id (customCT_sel A)
(λ _, Empty_set) (λ _, Empty_set) (λ _, unitO) _.
(** [customC]: [customCT] registered *)
Notation customC A := (inC (customCT A)).
Section customC.
  Context `{!customC A CON} {Σ}.
  (** [cif_own]: Own token *)
  Definition cif_own γ a : cif CON Σ :=
    cif_in (customCT A) (cifs_own γ a) nullary nullary ().

  Context `{!rust_haltGS TY Σ}.
  (** Semantics of [customCT] *)
  Definition customCT_sem `{inG Σ A} (s : customCT_sel A) : iProp Σ :=
    match s with
    | cifs_own γ a => own γ a
    end.
  #[export] Program Instance customCT_ecsem `{inG Σ A} {JUDG}
    : Ecsem (customCT A) CON JUDG Σ :=
    ECSEM (λ _ _ s _ _ _, customCT_sem s) _.
  Next Obligation. done. Qed.
End customC.
(** [customC] semantics registered *)
Notation customCS A := (inCS (customCT A)).

Section customC.
Context `{inG Σ A, !customC A CON, !Csem CON JUDG Σ, !rust_haltGS CON Σ,
    !customCS A CON JUDG Σ}.

(** Reify token *)
#[export] Program Instance own_as_cif {γ} {a : A} :
    AsCif CON (λ _, own γ a)%I := AS_CIF (cif_own γ a) _.
Next Obligation. move=>/= >. by rewrite sem_cif_in. Qed.
End customC.

(** ** Constructor and judgment constraint *)

(** Constructor constraint *)
Class rust_haltC CON A : Type := RUST_HALT_C {
rust_haltC_inv :: invC CON;
rust_haltC_na_inv :: na_invC CON;
rust_haltC_store :: storeC CON;
rust_haltC_borrow :: borrowC CON;
rust_haltC_proph_ag :: proph_agC nat xty CON;
rust_haltC_pborrow :: pborrowC nat xty CON;
rust_haltC_custom :: customC A CON;
}.

(** Judgment constraint *)
Class rust_haltJ CON JUDG Σ : Type := RUST_HALT_J {
rust_haltJ_inv :: invJ (cifO CON Σ) JUDG;
rust_haltJ_na_inv :: na_invJ (cifO CON Σ) JUDG;
rust_haltJ_store :: storeJ (cifO CON Σ) JUDG;
rust_haltJ_bupd :: bupdJ (cifOF CON $oi Σ) JUDG;
}.

(** Constructor semantics constraint *)
Class rust_haltCS CON JUDG `{inG Σ A, !rust_haltGS CON Σ, !rust_haltC CON A}
`{!rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ} : Prop := RUST_HALT_CS {
rust_haltCS_inv :: invCS CON JUDG Σ;
rust_haltCS_na_inv :: na_invCS CON JUDG Σ;
rust_haltCS_store :: storeCS CON JUDG Σ;
rust_haltCS_borrow :: borrowCS CON JUDG Σ;
rust_haltCS_proph_ag :: proph_agCS nat xty CON JUDG Σ;
rust_haltCS_pborrow :: pborrowCS nat xty CON JUDG Σ;
rust_haltCS_custom :: customCS A CON JUDG Σ;
}.

(** Judgment semantics constraint *)
Class rust_haltJS CON JUDG Σ `{inG Σ A, !rust_haltGS CON Σ, !rust_haltC CON A}
`{!rust_haltJ CON JUDG Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : Prop :=
RUST_HALT_JS {
rust_haltJS_inv :: invJS (cifOF CON) JUDG Σ;
rust_haltJS_na_inv :: na_invJS CON JUDG Σ;
rust_haltJS_store :: storeJS (cifOF CON) JUDG Σ;
rust_haltJS_bupd :: bupdJS (cifO CON Σ) JUDG (iProp Σ);
}.

(** ** World satisfaction *)

(** Modality for [borrow_wsat] *)
Definition borrowM `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}
  : iProp Σ → iProp Σ :=
  fupdw ⊤ ⊤ (inv_wsat ⟦⟧ᶜ ∗ dinv_wsat ⟦⟧ᶜ).
(** World satisfaction *)
Definition rust_halt_wsat
  `{!rust_haltGS CON Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)} : iProp Σ :=
  inv_wsat ⟦⟧ᶜ ∗ dinv_wsat ⟦⟧ᶜ ∗ borrow_wsat borrowM ⟦⟧ᶜ ∗ fborrow_wsat.

(** ** Lifetime inclusion *)

(** [LftIncl]: Type class for lifetime inclusion *)
Class LftIncl (κ α : lft) : Prop :=
  lft_incl' : κ ⊑ α.
Hint Mode LftIncl ! ! : typeclass_instances.

(** Trivial matches *)
#[export] Instance lft_incl'_top {κ} : LftIncl κ ⊤ | 2.
Proof. exact lft_incl_top. Qed.
#[export] Instance lft_incl'_refl {κ} : LftIncl κ κ | 2.
Proof. exact: lft_incl_refl. Qed.
(** Decompose the right-hand side *)
#[export] Instance lft_incl'_meet_intro `{!LftIncl κ α, !LftIncl κ β} :
  LftIncl κ (α ⊓ β) | 5.
Proof. exact: lft_incl_meet_intro. Qed.
(** Decompose the left-hand side *)
#[export] Instance lft_incl'_meet_by_l `{!LftIncl κ α} {κ'} :
  LftIncl (κ ⊓ κ') α | 30.
Proof. unfold LftIncl. etrans; [exact lft_incl_meet_l|done]. Qed.
#[export] Instance lft_incl'_meet_by_r `{!LftIncl κ' α} {κ} :
  LftIncl (κ ⊓ κ') α | 30.
Proof. unfold LftIncl. etrans; [exact lft_incl_meet_r|done]. Qed.

(** [LftIncl] is transitive *)
#[export] Instance lft_incl'_trans : Transitive LftIncl.
Proof. exact: lft_incl_trans. Qed.

(** Utility for [LftIncl] *)
Lemma lft_incl'_live_acc `{!lftG Σ} α `(!LftIncl κ α) {q} :
  q.[κ] ⊢ ∃ r, r.[α] ∗ (r.[α] -∗ q.[κ]).
Proof. exact: lft_incl_live_acc. Qed.
Lemma lft_incl'_sincl `{!lftG Σ} `(!LftIncl κ α) : ⊢ κ ⊑□ α.
Proof. exact: lft_incl_sincl. Qed.

(** ** Utility for the program logic *)

Section lrust.
  Context `{!lrustGS_gen hlc Σ}.

  (** Fuse points-to tokens *)
  Lemma heap_pointsto_vec_fuse {l q vl r wl} :
    l ↦∗{q} vl -∗ (l +ₗ length vl) ↦∗{r} wl -∗ ∃ s, l ↦∗{s} (vl ++ wl) ∗
      (l ↦∗{s} (vl ++ wl) -∗ l ↦∗{q} vl ∗ (l +ₗ length vl) ↦∗{r} wl).
  Proof.
    case (Qp.lower_bound q r)=> s[?[?[->->]]]. iIntros "[↦ ↦'] [↦+ ↦+']".
    iExists s. rewrite heap_pointsto_vec_app. iFrame "↦ ↦+". iIntros "[↦ ↦+]".
    iCombine "↦ ↦'" as "$". iCombine "↦+ ↦+'" as "$".
  Qed.
  Lemma heap_pointsto_just_vec_fuse {l q v r wl} :
    l ↦{q} v -∗ (l +ₗ 1) ↦∗{r} wl -∗ ∃ s, l ↦∗{s} (v :: wl) ∗
      (l ↦∗{s} (v :: wl) -∗ l ↦{q} v ∗ (l +ₗ 1) ↦∗{r} wl).
  Proof.
    setoid_rewrite <-heap_pointsto_vec_singleton. exact: heap_pointsto_vec_fuse.
  Qed.
  Lemma heap_pointsto_vec_just_fuse {l q vl r w} :
    l ↦∗{q} vl -∗ (l +ₗ length vl) ↦{r} w -∗ ∃ s, l ↦∗{s} (vl ++ [w]) ∗
      (l ↦∗{s} (vl ++ [w]) -∗ l ↦∗{q} vl ∗ (l +ₗ length vl) ↦{r} w).
  Proof.
    setoid_rewrite <-heap_pointsto_vec_singleton. exact: heap_pointsto_vec_fuse.
  Qed.
End lrust.

