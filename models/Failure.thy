theory Failure
  imports "../Soundness"
begin


section \<open> Util \<close>

(* TODO: move *)

lemma comp_inf_distrib:
  \<open>(a \<sqinter> b) \<circ> f = (a \<circ> f) \<sqinter> (b \<circ> f)\<close>
  by force

lemma comp_sup_distrib:
  \<open>(a \<squnion> b) \<circ> f = (a \<circ> f) \<squnion> (b \<circ> f)\<close>
  by force

lemma option_ex_split:
  \<open>(case mx of Some x \<Rightarrow> p x | None \<Rightarrow> q) \<longleftrightarrow> (\<exists>x. mx = Some x \<and> p x) \<or> mx = None \<and> q\<close>
  by (metis case_option_disj_iff)

lemma pred_times_le_iff:
  \<open>p \<times>\<^sub>P q \<le> p' \<times>\<^sub>P q' \<longleftrightarrow> p \<le> p' \<and> q \<le> q' \<or> p \<le> \<bottom> \<or> q \<le> \<bottom>\<close>
  by (force simp add: pred_times_def le_fun_def)

lemma pred_times_le_iff2:
  \<open>p \<times>\<^sub>P q \<le> p' \<times>\<^sub>P q' \<longleftrightarrow> p \<le> p' \<and> q \<le> q' \<or> (\<nexists>x. p x) \<or> (\<nexists>x. q x)\<close>
  by (force simp add: pred_times_def le_fun_def)

lemma eqpred_le_iff[simp]:
  \<open>(=) x \<le> (=) y \<longleftrightarrow> x = y\<close>
  by force

lemma eqpred_never_empty[simp]:
  \<open>(=) x \<le> \<bottom> \<longleftrightarrow> False\<close>
  by force

lemma (in order_bot) disj_leq_bot_iff[simp]:
  \<open>a \<le> \<bottom> \<or> a \<le> b \<longleftrightarrow> a \<le> b\<close>
  \<open>a \<le> b \<or> a \<le> \<bottom> \<longleftrightarrow> a \<le> b\<close>
  by (metis bot.extremum order_eq_iff)+


section \<open> Helper Lemmas \<close>

subsection \<open> State Capture \<close>

definition capture_fst (\<open>\<lceil> _ \<rceil>\<^sub>1\<close> [0] 999) where
  \<open>\<lceil> f \<rceil>\<^sub>1 \<equiv> \<lambda>(a,b). f a (a,b)\<close>

definition capture_snd (\<open>\<lceil> _ \<rceil>\<^sub>2\<close> [0] 999) where
  \<open>\<lceil> f \<rceil>\<^sub>2 \<equiv> \<lambda>(a,b). f b (a,b)\<close>

lemma capture_fst_apply[simp]:
  \<open>capture_fst f (a,b) = f a (a,b)\<close>
  by (simp add: capture_fst_def)

lemma capture_snd_apply[simp]:
  \<open>capture_snd f (a,b) = f b (a,b)\<close>
  by (simp add: capture_snd_def)

lemma capture_fst_unused[simp]:
  \<open>\<lceil> \<lambda>s. f \<rceil>\<^sub>1 = f\<close>
  by (simp add: capture_fst_def)

lemma capture_snd_unused[simp]:
  \<open>\<lceil> \<lambda>s. f \<rceil>\<^sub>2 = f\<close>
  \<open>\<lceil> \<lambda>s. f \<sqinter> g s \<rceil>\<^sub>2 = f \<sqinter> \<lceil> \<lambda>s. g s \<rceil>\<^sub>2\<close>
  \<open>\<lceil> \<lambda>s. g s \<sqinter> f \<rceil>\<^sub>2 = \<lceil> \<lambda>s. g s \<rceil>\<^sub>2 \<sqinter> f\<close>
  \<open>\<lceil> \<lambda>s. f \<squnion> g s \<rceil>\<^sub>2 = f \<squnion> \<lceil> \<lambda>s. g s \<rceil>\<^sub>2\<close>
  \<open>\<lceil> \<lambda>s. g s \<squnion> f \<rceil>\<^sub>2 = \<lceil> \<lambda>s. g s \<rceil>\<^sub>2 \<squnion> f\<close>
  by (force simp add: capture_snd_def)+

lemma capture_snd_idem[simp]:
  \<open>\<lceil> \<lambda>sa. \<lceil> \<lambda>sb. f sa sb \<rceil>\<^sub>2 \<rceil>\<^sub>2 = \<lceil> \<lambda>s. f s s \<rceil>\<^sub>2\<close>
  by (simp add: capture_snd_def)

notation(input) capture_snd (\<open>\<lceil> _ \<rceil>\<^sub>\<S>\<close> [0] 999)


abbreviation (in pre_perm_alg)
  \<open>all_disjoint_res \<equiv> \<lambda>a::'a. \<forall>b. \<not> a ## b\<close>


subsection \<open> Value at Location \<close>

definition val_at :: \<open>'a \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> bool\<close> (\<open>\<^bold>@\<close>) where
  \<open>\<^bold>@ x p \<equiv> \<lambda>f. p (f x)\<close>


subsection \<open> Tuple rearrangement \<close>

definition \<open>pApBC_to_ppABC \<equiv> \<lambda>(a,(b,c)). ((a,b),c)\<close>

lemma pApBC_to_ppACB_apply[simp]:
  \<open>pApBC_to_ppABC (a,b,c) = ((a,b),c)\<close>
  by (simp add: pApBC_to_ppABC_def split: prod.splits)

lemma pApBC_to_ppACB_inj:
  \<open>inj pApBC_to_ppABC\<close>
  by (simp add: pApBC_to_ppABC_def inj_def split: prod.splits)


definition \<open>ppABC_to_ppACB \<equiv> \<lambda>((a,b),c). ((a,c),b)\<close>

lemma ppABC_to_ppACB_apply[simp]:
  \<open>ppABC_to_ppACB ((a,b),c) = ((a,c),b)\<close>
  by (simp add: ppABC_to_ppACB_def split: prod.splits)

lemma ppABC_to_ppACB_inj:
  \<open>inj ppABC_to_ppACB\<close>
  by (simp add: ppABC_to_ppACB_def inj_def split: prod.splits)

lemma pred_times_ppABC_to_ppACB_local_left_eq[simp]:
  \<open>(\<L> p \<times>\<^sub>P q \<circ> ppABC_to_ppACB) = \<L> (p \<times>\<^sub>P q)\<close>
  by (simp add: fun_eq_iff sepconj_conj_def)

lemma subpred_pred_times_eq_res_ppABC_to_ppACB_iff:
  \<open>f \<le> (F \<times>\<^sub>P (=) x) \<circ> ppABC_to_ppACB \<longleftrightarrow> (\<exists>f'. f' \<le> F \<and> f = (f' \<times>\<^sub>P (=) x) \<circ> ppABC_to_ppACB)\<close>
  apply (clarsimp simp add: le_fun_def fun_eq_iff)
  apply (rule iffI)
   apply (rule_tac x=\<open>\<lambda>(ls, ss). f ((ls, x), ss)\<close> in exI, force)
  apply force
  done

lemma all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise:
  \<open>(\<forall>p\<le>(P \<times>\<^sub>P (=) x) \<circ> ppABC_to_ppACB. \<Q> p) \<longleftrightarrow> (\<forall>p\<le>P. \<Q> ((p \<times>\<^sub>P (=) x) \<circ> ppABC_to_ppACB))\<close>
  by (clarsimp simp add: subpred_pred_times_eq_res_ppABC_to_ppACB_iff, blast)

lemma pred_times_comp_ppABC_to_ppACB_eq[simp]:
  \<open>(pa \<times>\<^sub>P pb) \<times>\<^sub>P pc \<circ> ppABC_to_ppACB = (pa \<times>\<^sub>P pc) \<times>\<^sub>P pb\<close>
  by force

lemma pred_image_fst_pred_times_eq_res_ppABC_to_ppACB_eq[simp]:
  \<open>pred_image fst ((p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB) = pred_image fst p \<times>\<^sub>P q\<close>
  by (clarsimp simp add: fun_eq_iff)

lemma any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib:
  \<open>any_shared ((p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB) = (any_shared p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB\<close>
  by (simp add: any_shared_def)


\<comment> \<open> any_shared if of this form \<close>
lemma pred_image_fst_pred_times_eq_res_ppABC_to_ppACB_distrib:
  \<open>pred_image fst ((p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB) \<times>\<^sub>P qy =
    ((pred_image fst p \<times>\<^sub>P qy) \<times>\<^sub>P q) \<circ> ppABC_to_ppACB\<close>
  by (force simp add: fun_eq_iff)

lemma comp_ppABC_to_ppACB_mono[intro]:
  \<open>pa \<le> pb \<Longrightarrow> pa \<circ> ppABC_to_ppACB \<le> pb \<circ> ppABC_to_ppACB\<close>
  by (clarsimp simp add: le_fun_def)

lemma wssa_comp_ppABC_to_ppACB_distrib:
  \<open>wssa R (((p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB)) = ((wssa R p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB)\<close>
  by (force simp add: fun_eq_iff wlp_def)

lemma sswa_comp_ppABC_to_ppACB_distrib:
  \<open>sswa R (((p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB)) = ((sswa R p \<times>\<^sub>P q) \<circ> ppABC_to_ppACB)\<close>
  by (force simp add: fun_eq_iff sp_def)

lemma comp_ppABC_to_ppACB_comp_le_ppABC_to_ppACB_iff[simp]:
  \<open>(p \<circ> ppABC_to_ppACB) \<le> (q \<circ> ppABC_to_ppACB) \<longleftrightarrow> p \<le> q\<close>
  by (force simp add: le_fun_def)


section \<open> Failure \<close>

subsection \<open> Definitions \<close>

abbreviation
  \<open>nofailure_pred p \<equiv> (p \<times>\<^sub>P (=) Running) \<circ> ppABC_to_ppACB\<close>

abbreviation
  \<open>failure_pred p \<equiv> (p \<times>\<^sub>P (=) Failed) \<circ> ppABC_to_ppACB\<close>


lemma nofailure_pred_Inf_distrib:
  \<open>P \<noteq> {} \<Longrightarrow> nofailure_pred (Inf P) = Inf (nofailure_pred ` P)\<close>
  by (fastforce simp add: fun_eq_iff sepconj_conj_def)

lemma nofailure_pred_inf_distrib:
  \<open>nofailure_pred (pa \<sqinter> pb) = nofailure_pred pa \<sqinter> nofailure_pred pb\<close>
  by (fastforce simp add: fun_eq_iff sepconj_conj_def)

lemma nofailure_pred_Sup_semidistrib:
  \<open>nofailure_pred (Sup P) = Sup (nofailure_pred ` P)\<close>
  by (fastforce simp add: fun_eq_iff sepconj_conj_def)

lemma nofailure_pred_disj_distrib:
  \<open>nofailure_pred (pa \<squnion> pb) = nofailure_pred pa \<squnion> nofailure_pred pb\<close>
  by (force simp add: fun_eq_iff sepconj_conj_def)

\<comment> \<open> These two work because the fail_st resources are duplicable, i.e. \<open>a + a = a\<close>. \<close>
lemma nofailure_pred_sepconj_conj_distrib:
  \<open>nofailure_pred (pa \<^emph>\<and> pb) = nofailure_pred pa \<^emph>\<and> nofailure_pred pb\<close>
  using plus_fail_st_def
  by (force simp add: fun_eq_iff sepconj_conj_def)

lemma failure_pred_sepconj_conj_distrib:
  \<open>failure_pred (pa \<^emph>\<and> pb) = failure_pred pa \<^emph>\<and> failure_pred pb\<close>
  using plus_fail_st_def
  by (force simp add: fun_eq_iff sepconj_conj_def)


subsection \<open> Execution with failure \<close>

\<comment> \<open>
  A fairly standard result.
  Execution under failure avoidance can be broken into execution where the failure does not happen,
  and an assurance that the execution can't lead to failure.
\<close>
lemma sp_nofailure_pred_in_out_iff:
  fixes ra :: \<open>('a \<times> fail_st) \<times> 's \<Rightarrow> _ \<Rightarrow> bool\<close>
  shows
  \<open>sp ra (nofailure_pred p) \<le> nofailure_pred q \<longleftrightarrow>
    sp (ra \<circ>\<^sub>2 (\<lambda>(x, y). ((x, Running), y))) p \<le> q \<and>
    sp ra (nofailure_pred p) \<le> nofailure_pred \<top>\<close>
  by (force simp add: sp_def le_fun_def)


subsection \<open> Pretty RGSat failure judgmeent \<close>

abbreviation fl_rgsat_pretty
  (\<open>_, _, _, _, _ \<turnstile>\<^sub>f { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>R, G, I, F, T \<turnstile>\<^sub>f { p } c { q } \<equiv>
    rgsat c R G
      (nofailure_pred p) (nofailure_pred q)
      (nofailure_pred I) (nofailure_pred F)
      T\<close>

lemmas fl_rgsat_weaken =
  rgsat_weaken[where
    p'=\<open>nofailure_pred p'\<close> and q'=\<open>nofailure_pred q'\<close> and
    I'=\<open>nofailure_pred I'\<close> and F'=\<open>nofailure_pred F'\<close> and
    p=\<open>nofailure_pred p\<close> and q=\<open>nofailure_pred q\<close> and
    I=\<open>nofailure_pred I\<close> and F=\<open>nofailure_pred F\<close> for p q I F p' q' I' F', simplified]


section \<open> Assert \<close>

text \<open>
  Assert fails when its precondition is not met.
  GenRGSep has no embedded fail state, and so it must be encoded into the
  state model. Separation logic is not compatible with destructive failure,
  and, moreover, atoms see the whole state, not the local state.
  Thus we place a crash in the shared state.
\<close>
definition
  \<open>assert_rel p \<equiv> \<lambda>((l,fl),s) ((l',fl'),s').
    l' = l \<and> s' = s \<and> (
      p (l, s) \<and> fl = Running \<and> fl' = Running \<or> (\<not> p (l, s) \<or> fl = Failed) \<and> fl' = Failed)\<close>

abbreviation \<open>Assert p \<equiv> \<langle> assert_rel p \<rangle>\<close>
lemmas Assert_def = assert_rel_def


lemma rgsat_assert:
  assumes
    \<open>wssa R p \<^emph>\<and> F \<le> pa\<close>
    \<open>rel_image snd (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>wssa R p \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R p } Assert pa { wssa R p }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred p\<close> and q=\<open>wssa R (nofailure_pred p)\<close>])
  show
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (assert_rel pa) (wssa R (nofailure_pred p) \<^emph>\<and> f) \<le>
        wssa R (nofailure_pred p) \<^emph>\<and> any_shared f\<close>
    using assms(1)
    apply (simp add: assert_rel_def all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise)
    apply (clarsimp simp add: sp_def sepconj_conj_def le_fun_def wssa_comp_ppABC_to_ppACB_distrib)
    apply metis
    done

  show \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred p) \<^emph>\<and> nofailure_pred F) \<sqinter> assert_rel pa) \<le> G\<close>
    using assms(2)
    by (fastforce simp add: assert_rel_def nofailure_pred_sepconj_conj_distrib[symmetric]
        wssa_comp_ppABC_to_ppACB_distrib)
qed (simp add: wssa_comp_ppABC_to_ppACB_distrib sswa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+

lemma frame_expanding_iff:
  \<open>(\<forall>f\<le>F. (p \<sqinter> pa) \<^emph>\<and> f \<le> (p \<^emph>\<and> any_shared f) \<sqinter> pa) \<longleftrightarrow>
    ((p \<sqinter> pa) \<^emph>\<and> F \<le> (p \<^emph>\<and> F) \<sqinter> pa)\<close>
  by (simp add: le_fun_def any_shared_def sepconj_conj_def, fast)

lemma rgsat_assert2:
  assumes
    \<open>wssa R (p \<sqinter> pa) \<^emph>\<and> F \<le> pa\<close>
    \<open>rel_image snd (rel_liftL (wssa R (p \<sqinter> pa) \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>wssa R (p \<sqinter> pa) \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R (p \<sqinter> pa) } Assert pa { wssa R (p \<sqinter> pa) }\<close>
  using assms
  by (intro rgsat_assert) simp+

\<comment> \<open> slightly weaker than the full condition, but much more direct \<close>
lemma guard_frame_expanding_then_assert_framecond:
  \<open>wssa R pa \<^emph>\<and> F \<le> pa \<Longrightarrow> wssa R (p \<sqinter> pa) \<^emph>\<and> F \<le> pa\<close>
  by (meson inf_le2 order_trans sepconj_conj_monoL wlp_pred_mono)

lemma opstep_assert_iff[simp]:
  defines \<open>local \<equiv> fst \<circ> fst\<close>
    and \<open>failst \<equiv> snd \<circ> fst\<close>
    and \<open>shared \<equiv> snd\<close>
  shows
  \<open>opstep \<alpha> (s, Assert p) sc' \<longleftrightarrow>
    \<alpha> = Vis \<and>
    snd sc' = Skip \<and>
    (local (fst sc') = local s \<and>
      shared (fst sc') = shared s \<and>
      (p (local s, shared s) \<and> failst s = Running \<and> failst (fst sc') = Running \<or>
        (\<not> p (local s, shared s) \<or> failst s = Failed) \<and> failst (fst sc') = Failed))\<close>
  using assms
  by (force simp add: Assert_def case_prod_beta split_pairs2)


end