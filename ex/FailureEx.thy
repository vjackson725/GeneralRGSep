theory FailureEx
  imports "../Soundness"
begin

(* TODO: move *)

lemma non_dependent_all_concl_extract:
  \<open>p x \<Longrightarrow> (\<forall>x. p x \<longrightarrow> q \<and> r x) \<longleftrightarrow> (\<forall>x. p x \<longrightarrow> r x) \<and> q\<close>
  \<open>p x \<Longrightarrow> (\<forall>x. p x \<longrightarrow> r x \<and> q) \<longleftrightarrow> (\<forall>x. p x \<longrightarrow> r x) \<and> q\<close>
  by blast+
  


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


section \<open> Helper Lemmas \<close>

subsection \<open> Heap Lemmas \<close>

lemma heap_upd_eq_iff:
  \<open>ha(x \<mapsto>  va) = hb(x \<mapsto>  vb) \<longleftrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> ha y = hb y) \<and> va = vb\<close>
  by (force simp add: fun_eq_iff)

lemma map_empty_disjoint[simp]:
  \<open>Map.empty ## mb\<close>
  \<open>ma ## Map.empty\<close>
  by (simp add: disjoint_fun_def)+

lemma map_upd_disjoint[simp]:
  \<open>ma x = None \<Longrightarrow> ma(x := va) ## mb \<longleftrightarrow> va ## mb x \<and> ma ## mb\<close>
  \<open>mb x = None \<Longrightarrow> ma ## mb(x := vb) \<longleftrightarrow> ma x ## vb \<and> ma ## mb\<close>
   by (clarsimp simp add: disjoint_fun_def disjoint_option_def all_conj_distrib
      split: option.splits, fastforce)+

lemma map_empty_plus[simp]:
  \<open>Map.empty + mb = mb\<close>
  \<open>ma + Map.empty = ma\<close>
  by (simp add: fun_eq_iff)+

lemma not_dom_then_singleton_plus_heap_eq[simp]:
  \<open>h x = None \<Longrightarrow> [x \<mapsto> v] + h = h(x \<mapsto> v)\<close>
  by (simp add: fun_eq_iff)

lemma map_upd_None_over_plus_eq[simp]:
  \<open>mb x = None \<Longrightarrow> (ma + mb)(x := None) = (ma(x := None) + mb)\<close>
  \<open>ma x = None \<Longrightarrow> (ma + mb)(x := None) = (ma + mb(x := None))\<close>
  by fastforce+

lemma singleton_plus_heap_eq_iff:
  \<open>[x \<mapsto> va] + h = [x \<mapsto> vb] + h \<longleftrightarrow> Some va + h x = Some vb + h x\<close>
  by (simp add: plus_fun_def plus_option_def fun_eq_iff split: option.splits if_splits)

lemma heap_upd_eq_singleton_plus_heap_iff:
  \<open>hx(x \<mapsto>  va) = [x \<mapsto> vb] + hy \<longleftrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> hx y = hy y) \<and> Some vb + hy x = Some va\<close>
  by (force simp add: plus_fun_def plus_option_def fun_eq_iff split: option.splits if_splits)


subsubsection \<open> Value at Location \<close>

definition val_at :: \<open>'a \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> bool\<close> (\<open>\<^bold>@\<close>) where
  \<open>\<^bold>@ x p \<equiv> \<lambda>f. p (f x)\<close>

definition val_at_heap :: \<open>'a \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'v) \<Rightarrow> bool\<close> (\<open>\<^bold>@\<^sub>\<H>\<close>) where
  \<open>\<^bold>@\<^sub>\<H> pt p \<equiv> \<lambda>h. \<forall>v. h pt = Some v \<longrightarrow> p v\<close>


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


subsection \<open> Failure \<close>

subsection \<open> Definitions \<close>

abbreviation
  \<open>nofailure_pred p \<equiv> (p \<times>\<^sub>P (=) Running) \<circ> ppABC_to_ppACB\<close>

abbreviation
  \<open>failure_pred p \<equiv> (p \<times>\<^sub>P (=) Failed) \<circ> ppABC_to_ppACB\<close>

(*
lemma nofailure_pred_strong_mono[simp]:
  \<open>nofailure_pred p \<le> nofailure_pred q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: le_fun_def)

lemma nofailure_impl_failure_iff[simp]:
  \<open>nofailure_pred p \<le> failure_pred q \<longleftrightarrow> p \<le> \<bottom>\<close>
  by (simp add: le_fun_def)

lemma failure_impl_nofailure_iff[simp]:
  \<open>failure_pred p \<le> nofailure_pred q \<longleftrightarrow> p \<le> \<bottom>\<close>
  by (simp add: le_fun_def)
*)

\<comment> \<open> These two only work because the fail_st resources are duplicable, i.e. \<open>a + a = a\<close>. \<close>
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


section \<open> Heap Predicates \<close>

definition points_to :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<close> 90) where
  \<open>p \<^bold>\<mapsto> x \<equiv> (=) [p \<mapsto> x]\<close>

definition points_to_dom_upcl :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<^sup>\<Up>\<close> 90) where
  \<open>p \<^bold>\<mapsto>\<^sup>\<Up> x \<equiv> \<lambda>h. h p = Some x\<close>


lemma points_to_dom_upcl_eq:
  fixes x :: \<open>'a :: perm_alg\<close>
  assumes maximal_res: \<open>\<forall>x'. \<not> x \<prec> x'\<close>
  shows \<open>pt \<^bold>\<mapsto>\<^sup>\<Up> x = \<top> \<^emph> pt \<^bold>\<mapsto> x\<close>
  unfolding sepconj_def points_to_def points_to_dom_upcl_def
  apply (clarsimp simp add: fun_eq_iff)
  apply (rename_tac h)
  apply (intro iffI)
   apply (rule_tac x=\<open>h(pt := None)\<close> in exI)
   apply (rule_tac x=\<open>[pt \<mapsto> x]\<close> in exI)
   apply force
  apply (clarsimp simp add: disjoint_option_def plus_option_def all_conj_distrib
      split: option.splits)
  apply (cut_tac maximal_res)
  apply (metis disjoint_fun_def disjoint_option_simps(1) partial_le_plus2
      resource_order.le_neq_trans)
  done


(*
definition points_to_perm
  :: \<open>'pt \<Rightarrow> 'perm \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> ('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> 's \<Rightarrow> bool\<close>
  (\<open>_ \<^bold>\<mapsto>\<^bsub>_\<^esub> _\<close> [90,0,90] 90)
  where
  \<open>pt \<^bold>\<mapsto>\<^bsub>perm\<^esub> e \<equiv> \<lambda>(ls,ss). (=) [pt \<mapsto> (Discr (e ss), perm)] ls\<close>
*)


definition \<open>maximal_heap \<equiv> \<lambda>h. \<forall>pt. h pt \<noteq> None\<close>

definition
  \<open>heap_avoiding \<rho> v \<pi> \<equiv> - (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). \<rho> \<^bold>\<mapsto>\<^sup>\<Up> x')\<close>

lemma res_disjoint_to_memcell_le_heap_avoiding:
  \<open>(#/#) [\<rho> \<mapsto> (Discr v, \<pi>)] \<le> heap_avoiding \<rho> v \<pi>\<close>
  by (clarsimp simp add: heap_avoiding_def le_fun_def points_to_dom_upcl_def
      disjoint_fun_def disjoint_option_def split: option.splits)


lemma top_write_heap_avoiding_iff_all_disjoint_perm:
  fixes \<pi> :: \<open>'p::pre_perm_alg\<close>
  shows \<open>\<top> \<le> \<L> (heap_avoiding \<rho> v \<pi>) \<longleftrightarrow> (\<forall>\<pi>'. \<not> \<pi> ## \<pi>')\<close>
  by (force simp add: heap_avoiding_def points_to_dom_upcl_def le_fun_def)


abbreviation \<open>heap_pred p \<equiv> (p \<times>\<^sub>P \<top>) \<circ> ppABC_to_ppACB\<close>


section \<open> Heap Commands \<close>

subsection \<open> Heap Read \<close>

definition heap_read_rel
  :: \<open>('v \<Rightarrow> 'u) \<Rightarrow> 'x \<Rightarrow> 'pt \<Rightarrow>
        (('pt \<rightharpoonup> 'v) \<times> fail_st) \<times> ('x \<Rightarrow> 'u) \<Rightarrow>
        (('pt \<rightharpoonup> 'v) \<times> fail_st) \<times> ('x \<Rightarrow> 'u) \<Rightarrow>
        bool\<close>
  where
    \<open>heap_read_rel f x pt \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        (\<exists>v. l pt = Some v \<and> l' = l \<and> s' = s(x := f v) \<and> fl' = Running) \<or>
        (l pt = None \<or> fl = Failed) \<and> l' = l \<and> s' = s \<and> fl' = Failed\<close>

abbreviation \<open>HeapRead f x pt \<equiv> \<langle> heap_read_rel f x pt \<rangle>\<close>
lemmas HeapRead_def = heap_read_rel_def


lemma rgsat_heap_read:
  fixes X :: 'u
    and p :: \<open>('x \<Rightarrow> 'u) \<Rightarrow> bool\<close>
    and x :: 'x
    and e :: \<open>('x \<Rightarrow> 'u) \<Rightarrow> 'v::pre_perm_alg\<close>
    and R \<pi> pt u2v
  defines \<open>heap_read_G \<equiv> (\<lambda>s s'. s' = s(x := u2v (e s)))\<close>
  defines\<open>precond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> ((\<lambda>ss. p (ss(x := u2v (e ss)))) \<sqinter> \<^bold>@ x ((=) X))\<close>
  defines \<open>postcond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e (ss(x := X))) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
  defines \<open>frame_post :: (('a \<rightharpoonup> 'v) \<times> ('x \<Rightarrow> 'u) \<Rightarrow> bool) \<equiv>
    \<lceil>\<lambda>ss. \<L> (\<^bold>@ pt (\<lambda>mvf. \<forall>vf. mvf = Some vf \<longrightarrow>
                          (p (ss(x := u2v (e ss))) \<longrightarrow> p (ss(x := u2v (e ss + vf)))) )) \<rceil>\<^sub>\<S>\<close>
  assumes
    \<open>heap_read_G \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_cond:
    \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R precond } HeapRead u2v x pt { sswa R postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  let ?ra = \<open>(\<lambda>(ls, ss) (ls', ss'). ls' = ls \<and> (\<exists>v. ls pt = Some v \<and> ss' = ss(x := u2v v)))\<close>

  have nofailure_helper:
    \<open>\<And>f. sp (heap_read_rel u2v x pt) (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>\<close>
    apply (clarsimp simp add: heap_read_rel_def sp_def)
    apply (elim disjE, force)
    apply (force simp add: precond_def wlp_def val_at_def points_to_def sepconj_conj_def
        plus_option_iff)
    done
  have rel_helper:
    \<open>(heap_read_rel u2v x pt \<circ>\<^sub>2 (\<lambda>(x, y). ((x, Running), y))) = ?ra\<close>
    by (force simp add: heap_read_rel_def fun_eq_iff)

  let ?frame2 = \<open>\<forall>f\<le>F. sp ?ra (wssa R precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F. sp (heap_read_rel u2v x pt) (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
      nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have \<open>\<top> = (F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post)\<close>
    using frame_cond
    by simp
  also have \<open>... = ?frame2\<close>
    apply (clarsimp simp add: le_fun_def sp_def imp_ex_conjL imp_conjL sepconj_conj_def
        septract_conj_def)
    apply (intro iffI impI allI)
      (* \<Rightarrow> *)
     apply (rename_tac f lfs v ss ls fs)
     apply (drule spec2, drule mp, fast)
     apply (drule spec, drule mp, rule disjoint_sym, assumption, drule mp, assumption)
     apply (clarsimp simp add: precond_def postcond_def)
     apply (simp add: wlp_def val_at_def points_to_def frame_post_def
        plus_option_iff disjoint_option_iff)
     apply (subgoal_tac \<open>ls pt = Some (e ss) \<and> (\<forall>pt'. pt' \<noteq> pt \<longrightarrow> ls pt' = None)\<close>)
      prefer 2
      apply (metis fun_upd_other fun_upd_same rtranclp.rtrancl_refl)
     apply clarsimp
     apply (elim disjE conjE exE)
      (* ls:Some/fs:None *)
      apply fastforce
      (* h:Some/f:Some *)
     apply (rule_tac x=fs in exI)
     apply (rule conjI, force)
     apply (rule conjI, force)
     apply (rule conjI[rotated], force)
     apply force
      (* \<Leftarrow> *)
    apply (rename_tac fs ss ls)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, fast)
    apply (subgoal_tac \<open>ls = [pt \<mapsto> e ss]\<close>)
     prefer 2
     apply (fastforce simp add: precond_def wlp_def points_to_def)
    apply (case_tac \<open>fs pt\<close>)
      (** \<open>fs pt = None\<close> *)
     apply (simp add: frame_post_def val_at_def; fail)
      (** \<open>fs pt = Some ...\<close> *)
    apply (rename_tac vf)
    apply (drule_tac x=\<open>ls + fs\<close> and y=\<open>e ss + vf\<close> in spec2, drule mp, force)
    apply clarsimp
    apply (drule_tac x=\<open>[pt \<mapsto> e ss]\<close> in spec)
    apply (simp add: postcond_def frame_post_def)
    apply (clarsimp simp add: disjoint_sym_iff val_at_def points_to_def fun_eq_iff plus_option_iff
        if_distrib[of \<open>\<lambda>x. x = _\<close>] if_distrib[of \<open>\<lambda>x. x + _ = _\<close>] if_bool_eq_conj all_conj_distrib
        eq_commute[of _ \<open>_ pt\<close>])
    done
  also have \<open>... = ?frame1\<close>
    apply (simp add: wssa_comp_ppABC_to_ppACB_distrib)
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib pred_times_le_iff)
    apply (subst sp_nofailure_pred_in_out_iff)
    apply (simp add: nofailure_helper rel_helper)
    done
  finally show
    \<open>\<forall>f\<le>nofailure_pred F. sp (heap_read_rel u2v x pt) (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
      nofailure_pred postcond \<^emph>\<and> any_shared f\<close>
    unfolding any_shared_def precond_def postcond_def
    by simp

  show \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred precond) \<^emph>\<and>
          nofailure_pred F) \<sqinter> heap_read_rel u2v x pt) \<le> G\<close>
    using assms(5)
    unfolding heap_read_G_def precond_def
    apply (clarsimp simp add: wssa_comp_ppABC_to_ppACB_distrib heap_read_rel_def sepconj_conj_def
        plus_option_iff ex_disj_distrib conj_disj_distribR wlp_def points_to_def val_at_def)
    sledgehammer
    sorry
qed (simp add: sswa_comp_ppABC_to_ppACB_distrib wssa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+


subsection \<open> Heap Write \<close>

definition heap_upd_rel
  :: \<open>'pt \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'a) \<Rightarrow> ((('pt \<rightharpoonup> 'a) \<times> fail_st) \<times> 's) \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>heap_upd_rel pt e \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        s' = s \<and> (
          (\<exists>v. l pt = Some v \<and> fl = Running \<and> l' = l(pt \<mapsto> e v s) \<and> fl' = Running) \<or>
          (l pt = None \<or> fl = Failed) \<and> l' = l \<and> fl' = Failed)\<close>

abbreviation \<open>HeapUpd pt e \<equiv> \<langle> heap_upd_rel pt e \<rangle>\<close>

lemma rgsat_heap_update:
  fixes e :: \<open>'s \<Rightarrow> 'v::pre_perm_alg\<close>
    and e' :: \<open>'v \<Rightarrow> 's \<Rightarrow> 'v\<close>
    and pt \<pi> p R
  defines \<open>precond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
    and \<open>postcond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e' (e ss) ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
    and \<open>frame_post \<equiv>
          \<lceil> \<lambda>ss. \<L> (\<^bold>@\<^sub>\<H> pt (\<lambda>vf. e' (e ss) ss ## vf \<and> e' (e ss + vf) ss = e' (e ss) ss + vf)) \<rceil>\<^sub>\<S>\<close>
  assumes
    \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post\<close>
    \<open>(=) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R precond } HeapUpd pt e' { sswa R postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])

  have helper:
    \<open>\<And>f. (\<lambda>(l', s'). l' pt = None) \<sqinter> (wssa R precond \<^emph>\<and> f) \<le> \<bottom>\<close>
    apply (clarsimp simp add: precond_def points_to_def fun_eq_iff sp_def sepconj_conj_def wlp_def
        plus_option_iff split: prod.splits)
    apply (metis not_None_eq rtranclp.rtrancl_refl)
    done

  let ?ra = \<open>\<lambda>(l, s) (l', s'). s' = s \<and> (\<exists>v. l pt = Some v \<and> l' = l(pt \<mapsto> e' v s))\<close>

  let ?frame2 = \<open>\<forall>f\<le>F. sp ?ra (wssa R precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (heap_upd_rel pt e') (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
        nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have helper1: \<open>(heap_upd_rel pt e' \<circ>\<^sub>2 (\<lambda>(x, y). ((x, Running), y))) = ?ra\<close>
    by (clarsimp simp add: heap_upd_rel_def fun_eq_iff)
  have helper2:
    \<open>\<And>f. sp (heap_upd_rel pt e') (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>\<close>
    unfolding heap_upd_rel_def precond_def
    by (force simp add: sepconj_conj_apply sp_def plus_option_iff wlp_def points_to_def)

  have \<open>\<top> = (F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post)\<close>
    using assms(4) by simp
  also have \<open>(F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> frame_post) = ?frame2\<close>
    apply (clarsimp simp add: sp_def le_fun_def sepconj_conj_def)
    apply (rule iffI)
      (* \<Rightarrow> *)
     apply (clarsimp simp add: imp_conjL plus_option_iff)
     apply (rename_tac f ss v ls fs)
     apply (drule spec2, drule mp, blast)
     apply (drule mp, simp add: septract_conj_def, metis disjoint_sym)
     apply (clarsimp simp add: precond_def postcond_def frame_post_def wlp_def points_to_def
        disjoint_option_iff)
     apply (case_tac \<open>ls pt = None\<close>)
      (** \<open>ls pt = None\<close> *)
      apply force
      (** \<open>ls pt = Some ...\<close> *)
     apply (clarsimp simp add:  plus_option_iff wlp_def)
     apply (rename_tac v)
     apply (subgoal_tac \<open>ls pt = Some (e ss) \<and> (\<forall>pt'. pt' \<noteq> pt \<longrightarrow> ls pt' = None)\<close>)
      prefer 2
      apply fastforce
     apply (clarsimp simp add: plus_option_def wlp_def disjoint_option_iff split: option.splits)
      (* as there is only one source of a frame that passes predicate \<open>f\<close>, there is only one
          frame that will work here. *)
     apply (rule_tac x=fs in exI)
     apply (rule conjI, force simp add: val_at_heap_def)
     apply (elim disjE; simp?)
      (*** \<open> fs pt = None \<close> *)
      apply (force simp add: fun_eq_iff)
      (*** \<open> fs pt = Some ... \<close> *)
     apply (clarsimp simp add: fun_eq_iff if_bool_eq_disj if_distrib[of \<open>\<lambda>x. x = _\<close>] val_at_heap_def)
     apply metis
      (* \<Leftarrow> *)
    apply (clarsimp simp add: septract_conj_def imp_ex_conjL imp_conjL)
    apply (rename_tac fs ss ls)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, blast)
    apply (drule_tac x=ss in spec)
    apply (drule_tac x=\<open>ls + fs\<close> in spec)
    apply (subgoal_tac \<open>ls pt = Some (e ss)\<close>)
     prefer 2
     apply (force simp add: precond_def wlp_def points_to_def)
    apply (case_tac \<open>fs pt\<close>)
      (*** \<open> fs pt = None \<close> *)
     apply (drule_tac x=\<open>e ss\<close> in spec)
     apply (drule mp, force simp add: precond_def points_to_def)
     apply clarsimp
     apply (drule spec, drule mp, rule disjoint_sym, assumption)
     apply (simp add: postcond_def frame_post_def val_at_heap_def; fail)
      (*** \<open> fs pt = Some ... \<close> *)
    apply (clarsimp simp add: plus_option_iff imp_conjL)
    apply (drule spec, drule mp, rule disjoint_sym, assumption)
    apply clarsimp
    apply (simp add: precond_def postcond_def frame_post_def val_at_heap_def points_to_def
        heap_upd_eq_singleton_plus_heap_iff; fail)
    done
  also have \<open>... = ?frame1\<close>
    apply (simp add: wssa_comp_ppABC_to_ppACB_distrib)
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib pred_times_le_iff)
    apply (subst sp_nofailure_pred_in_out_iff)
    apply (simp add: helper1 helper2)
    done
  finally show ?frame1
    using assms(3)
    by clarsimp

  show
    \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred precond) \<^emph>\<and> nofailure_pred F) \<sqinter>
      heap_upd_rel pt e') \<le> G\<close>
    using assms(5)
    unfolding precond_def  heap_upd_rel_def
    by fastforce
qed (simp add: sswa_comp_ppABC_to_ppACB_distrib wssa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+


subsection \<open> Heap Alloc \<close>

definition heap_alloc_rel
  :: \<open>('pt \<Rightarrow> 'a::pre_perm_alg) \<Rightarrow> 'x \<Rightarrow> (('x \<Rightarrow> 'a) \<Rightarrow> 'a) \<Rightarrow>
        ((('pt \<rightharpoonup> 'a) \<times> fail_st) \<times> ('x \<Rightarrow> 'a)) \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>heap_alloc_rel Ptr x e \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        (\<exists>pt.
          l pt = None \<and> l' = l(pt \<mapsto> e s) \<and>
          s' = s(x := Ptr pt) \<and>
          fl = Running \<and> fl' = fl) \<or>
        (fl = Failed \<or> (\<forall>pt. l pt \<noteq> None)) \<and>
          l' = l \<and> s' = s \<and> fl' = Failed\<close>

abbreviation \<open>HeapAlloc Ptr x e \<equiv> \<langle> heap_alloc_rel Ptr x e \<rangle>\<close>

lemma rgsat_heap_alloc:
  fixes p pt e R F x X Ptr
  defines \<open>precond \<equiv> \<L> emp \<sqinter> \<S> (p \<sqinter> \<^bold>@ x ((=) X))\<close>
  defines \<open>postcond \<equiv> \<Squnion>pt. \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e (ss(x := X))) \<rceil>\<^sub>\<S> \<sqinter> \<S> (\<lambda>ss. p (ss(x := X)) \<and> ss x = Ptr pt)\<close>
  assumes
    \<open>(\<lambda>s s'. \<exists>pt. s' = s(x := Ptr pt)) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_cond: \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> - \<L> maximal_heap\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R precond } HeapAlloc Ptr x e { sswa R postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])

  let ?ra = \<open>\<lambda>(l, s) (l', s'). 
              \<exists>pt.
                l pt = None \<and> l' pt = Some (e s) \<and>
                (\<forall>pt'. pt' \<noteq> pt \<longrightarrow> l' pt' = l pt') \<and>
                s' x = Ptr pt \<and>
                (\<forall>x'. x' \<noteq> x \<longrightarrow> s' x' = s x')\<close>

  have atomrel_helper: \<open>heap_alloc_rel Ptr x e \<circ>\<^sub>2 (\<lambda>(x, y). ((x, Running), y)) = ?ra\<close>
    by (clarsimp simp add: fun_eq_iff heap_alloc_rel_def all_conj_distrib)

  have
    \<open>(F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> - \<L> maximal_heap) =
      (\<forall>f\<le>F. sp (heap_alloc_rel Ptr x e) (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>)\<close>
    apply (clarsimp simp add: sp_def sepconj_conj_apply septract_conj_def le_fun_def
        imp_conjL imp_ex_conjL)
    apply (intro iffI allI impI)
      (* \<Rightarrow> *)
     apply (rename_tac lsf' fl' ss' ss ls fs)
     apply (drule spec2, drule mp, blast)
     apply (drule spec, drule mp, rule disjoint_sym, assumption, drule mp, assumption)
     apply (clarsimp simp add: heap_alloc_rel_def)
     apply (elim disjE, fast)
     apply (clarsimp simp add: plus_option_iff ex_disj_distrib wlp_def emp_def
        precond_def maximal_heap_def)
     apply (drule_tac x=pt in spec)
     apply force
        (* \<Leftarrow> *)
    apply clarsimp
    apply (drule spec, drule mp, fast)
    apply (clarsimp simp add: heap_alloc_rel_def all_conj_distrib precond_def wlp_def emp_def
        imp_ex_conjL imp_conjL maximal_heap_def)
    apply (rename_tac fs ss ls)
    apply (drule_tac x=fs in spec, drule mp[of \<open>All _\<close>], fast)
    apply (metis map_empty_disjoint(1) map_empty_plus(1))
    done
  then have nofailure_helper:
    \<open>\<forall>f\<le>F. sp (heap_alloc_rel Ptr x e) (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>\<close>
    using frame_cond
    by simp

  let ?frame2 = \<open>\<forall>f\<le>F. sp ?ra (wssa R precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (heap_alloc_rel Ptr x e) (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
        nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have \<open>\<top> = ?frame2\<close>
    apply clarsimp
    apply (clarsimp simp add: precond_def postcond_def sp_def emp_def sepconj_conj_def wlp_def
        points_to_def)
    apply (rename_tac f lfs' ss' ss pt ls fs)
    apply (subgoal_tac \<open>ls = Map.empty\<close>)
     prefer 2
     apply blast
    apply clarsimp
    apply (subgoal_tac \<open>ss'(x := X) = ss\<close>)
     prefer 2
     apply (fastforce simp add: val_at_def)
    apply simp \<comment> \<open> do \<^emph>\<open>not\<close> clarify \<close>
    apply (thin_tac \<open>ss'(x := X) = ss\<close>)
    apply (rule_tac x=\<open>[pt \<mapsto> e ss]\<close> in exI)
    apply (rule_tac x=fs in exI)
    apply force
    done
  also have \<open>?frame2 = ?frame1\<close>
    apply (simp add: wssa_comp_ppABC_to_ppACB_distrib)
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib pred_times_le_iff)
    apply (subst sp_nofailure_pred_in_out_iff)
    apply (clarsimp simp add: atomrel_helper nofailure_helper)
    done
  finally show \<open>?frame1\<close>
    by simp

  show
    \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred precond) \<^emph>\<and> nofailure_pred F) \<sqinter>
      heap_alloc_rel Ptr x e) \<le> G\<close>
    using assms(3) frame_cond
    unfolding heap_alloc_rel_def precond_def maximal_heap_def
    apply (clarsimp simp add: nofailure_pred_sepconj_conj_distrib[symmetric] emp_def wlp_def
         sepconj_conj_def le_fun_def val_at_def plus_option_iff septract_conj_def imp_ex_conjL
         imp_conjL)
    apply (rename_tac ss ss' fl ls fs fls' fl')
    apply (subgoal_tac \<open>ls = Map.empty\<close>)
     prefer 2
     apply fast
    apply (elim disjE, blast)
    apply clarsimp
    apply (drule spec2, drule mp, assumption)
    apply (metis fail_st.distinct(1) map_empty_disjoint(2) option.distinct(1) rtranclp.rtrancl_refl)
    done
qed (simp add: sswa_comp_ppABC_to_ppACB_distrib wssa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+


subsection \<open> Heap Free \<close>

definition heap_free_rel
  :: \<open>'pt \<Rightarrow> ((('pt \<rightharpoonup> 'a::pre_perm_alg) \<times> fail_st) \<times> 's) \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>heap_free_rel pt \<equiv>
      (\<lambda>(l,fl) (l',fl').
        (\<exists>x. l pt = Some x \<and> l' = l(pt := None)) \<and> fl = Running \<and> fl' = fl \<or>
        (fl = Failed \<or> l pt = None) \<and> l' = l \<and> fl' = Failed
      ) \<times>\<^sub>R (=)\<close>

abbreviation \<open>HeapFree pt \<equiv> \<langle> heap_free_rel pt \<rangle>\<close>

lemma rgsat_heap_free:
  fixes pt e R p
    and \<pi> :: \<open>'perm :: pre_perm_alg\<close>
  defines \<open>precond \<equiv> (\<Squnion>v. \<L> (pt \<^bold>\<mapsto> v)) \<sqinter> \<S> p\<close>
    and \<open>postcond \<equiv> \<L> emp \<sqinter> \<S> p\<close>
  assumes
    \<open>(=) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_cond:
    \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> - \<L> (\<Squnion>v. pt \<^bold>\<mapsto>\<^sup>\<Up> v)\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R precond } HeapFree pt { sswa R postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  let ?ra = \<open>(\<lambda>l l'. (\<exists>x. l pt = Some x \<and> l' = l(pt := None))) \<times>\<^sub>R (=)\<close>

  have \<open>\<And>f. sp (heap_free_rel pt) (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred \<top>\<close>
    unfolding heap_free_rel_def precond_def
    apply (clarsimp simp add: sp_def wlp_def points_to_def sepconj_conj_def plus_option_iff)
    apply (metis (full_types) fun_upd_same not_None_eq rtranclp.rtrancl_refl)
    done
  then have heap_free_rel_nofailure_helper:
    \<open>\<And>f q.
      sp (heap_free_rel pt) (nofailure_pred (wssa R precond \<^emph>\<and> f)) \<le> nofailure_pred q \<longleftrightarrow>
        sp ?ra (wssa R precond \<^emph>\<and> f) \<le> q\<close>
    apply (subst sp_nofailure_pred_in_out_iff)
    apply (clarsimp simp add: heap_free_rel_def sp_def le_fun_def sepconj_conj_def)
    done

  let ?frame2 = \<open>\<forall>f\<le>F. sp ?ra (wssa R precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
          sp (heap_free_rel pt) (wssa R (nofailure_pred precond) \<^emph>\<and> f) \<le>
            nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have \<open>\<top> = (F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> - \<L> (\<Squnion>v. pt \<^bold>\<mapsto>\<^sup>\<Up> v))\<close>
    using frame_cond
    by simp
  also have \<open>... = ?frame2\<close>
    apply (clarsimp simp add: sepconj_conj_def sp_def le_fun_def imp_conjL imp_ex_conjL
        plus_option_iff septract_conj_def)
    apply (intro iffI allI impI; clarify?)
      (* \<Rightarrow> *)
     apply (rename_tac ss ls fs vv)
     apply (drule_tac spec2, drule mp, fast, drule spec, drule mp, rule disjoint_sym, assumption)
     apply (drule mp, fast)
     apply (subgoal_tac \<open>\<exists>v. ls = [pt \<mapsto> v]\<close>)
      prefer 2
      apply (simp add: precond_def wlp_def points_to_def, blast)
     apply (simp add: precond_def postcond_def)
     apply (clarsimp simp add: emp_def wlp_def points_to_def points_to_dom_upcl_def)
     apply blast
      (* \<Leftarrow> *)
    apply (rename_tac fs ss ls vf)
    apply (clarsimp simp add: points_to_dom_upcl_def)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, fast)
    apply (subgoal_tac \<open>\<exists>v. ls = [pt \<mapsto> v]\<close>)
     prefer 2
     apply (simp add: precond_def wlp_def points_to_def, blast)
    apply clarsimp
    apply (drule_tac x=\<open>[pt \<mapsto> v] + fs\<close> in spec, drule mp, force)
    apply (drule_tac x=\<open>[pt \<mapsto> v]\<close> in spec, drule mp)
     apply (simp add: disjoint_sym_iff; fail)
    apply (clarsimp simp add: postcond_def emp_def fun_eq_iff split: if_splits)
    done
  also have \<open>... = ?frame1\<close>
    by (simp add: pred_times_le_iff heap_free_rel_nofailure_helper
        all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib
        nofailure_pred_sepconj_conj_distrib[symmetric] wssa_comp_ppABC_to_ppACB_distrib)
  finally show \<open>?frame1\<close>
    unfolding postcond_def emp_def
    by simp

  show
    \<open>rel_image snd (rel_liftL (wssa R (nofailure_pred precond) \<^emph>\<and> nofailure_pred F) \<sqinter>
      heap_free_rel pt) \<le> G\<close>
    using assms(3)
    by (fastforce simp add: heap_free_rel_def)
qed (simp add: sswa_comp_ppABC_to_ppACB_distrib wssa_comp_ppABC_to_ppACB_distrib pred_times_le_iff)+


end