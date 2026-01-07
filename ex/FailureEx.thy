theory FailureEx
  imports "../Soundness"
begin

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


section \<open> Helper Lemmas \<close>

subsection \<open> Heap Lemmas \<close>

lemma heap_upd_eq_iff:
  \<open>ha(x \<mapsto>  va) = hb(x \<mapsto>  vb) \<longleftrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> ha y = hb y) \<and> va = vb\<close>
  by (force simp add: fun_eq_iff)

lemma not_dom_then_singleton_plus_heap_eq[simp]:
  \<open>h x = None \<Longrightarrow> [x \<mapsto> v] + h = h(x \<mapsto> v)\<close>
  by (simp add: fun_eq_iff)

lemma map_empty_disjoint[simp]:
  \<open>Map.empty ## mb\<close>
  \<open>ma ## Map.empty\<close>
  by (simp add: disjoint_fun_def)+

lemma map_empty_plus[simp]:
  \<open>Map.empty + mb = mb\<close>
  \<open>ma + Map.empty = ma\<close>
  by (simp add: fun_eq_iff)+

lemma singleton_plus_heap_eq_iff:
  \<open>[x \<mapsto> va] + h = [x \<mapsto> vb] + h \<longleftrightarrow> Some va + h x = Some vb + h x\<close>
  by (simp add: plus_fun_def plus_option_def fun_eq_iff split: option.splits if_splits)

lemma heap_upd_eq_singleton_plus_heap_iff:
  \<open>hx(x \<mapsto>  va) = [x \<mapsto> vb] + hy \<longleftrightarrow> (\<forall>y. y \<noteq> x \<longrightarrow> hx y = hy y) \<and> Some vb + hy x = Some va\<close>
  by (force simp add: plus_fun_def plus_option_def fun_eq_iff split: option.splits if_splits)


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


subsection \<open> X \<close>

\<comment> \<open> A 'local' predicate that may depend on the shared state. \<close>
abbreviation(input) local_pred_with_shared
  :: \<open>('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<^sub>S\<close>)
  where
    \<open>\<L>\<^sub>S p \<equiv> \<lambda>(ls, ss). p ss ls\<close>



subsection \<open> Failure \<close>

subsection \<open> Definitions \<close>

abbreviation
  \<open>nofailure_pred p \<equiv> (p \<times>\<^sub>P (=) Running) \<circ> ppABC_to_ppACB\<close>

abbreviation
  \<open>failure_pred p \<equiv> (p \<times>\<^sub>P (=) Failed) \<circ> ppABC_to_ppACB\<close>

lemma nofailure_pred_strong_mono[simp]:
  \<open>nofailure_pred p \<le> nofailure_pred q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: le_fun_def)

\<comment> \<open> These two only work because the fail_st resources are duplicable, i.e. \<open>a + a = a\<close>. \<close>
lemma nofailure_pred_sepconj_conj_distrib:
  \<open>nofailure_pred (pa \<^emph>\<and> pb) = nofailure_pred pa \<^emph>\<and> nofailure_pred pb\<close>
  using plus_fail_st_def
  by (force simp add: fun_eq_iff sepconj_conj_def)

lemma failure_pred_sepconj_conj_distrib:
  \<open>failure_pred (pa \<^emph>\<and> pb) = failure_pred pa \<^emph>\<and> failure_pred pb\<close>
  using plus_fail_st_def
  by (force simp add: fun_eq_iff sepconj_conj_def)


abbreviation failure_rgsat_pretty
  (\<open>_, _, _, _, _ \<turnstile>\<^sub>f { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>R, G, I, F, T \<turnstile>\<^sub>f { p } c { q } \<equiv>
    rgsat c R G
      (nofailure_pred p) (nofailure_pred q)
      (nofailure_pred I) (nofailure_pred F)
      T\<close>


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
    \<open>p \<^emph>\<and> F \<le> pa\<close>
    \<open>rel_image snd (rel_liftL (p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R p } Assert pa { sswa R p }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred p\<close> and q=\<open>nofailure_pred p\<close>])
  show
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (assert_rel pa) (nofailure_pred p \<^emph>\<and> f) \<le> nofailure_pred p \<^emph>\<and> any_shared f\<close>
    using assms(1)
    apply (simp add: assert_rel_def all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise)
    apply (clarsimp simp add: sp_def sepconj_conj_def)
    apply blast
    done

  show \<open>rel_image snd (rel_liftL (nofailure_pred p \<^emph>\<and> nofailure_pred F) \<sqinter> assert_rel pa) \<le> G\<close>
    using assms(2)
    by (fastforce simp add: nofailure_pred_sepconj_conj_distrib[symmetric] assert_rel_def)
qed (clarsimp simp add: wlp_def sp_def le_fun_def)+

lemma frame_expanding_iff:
  \<open>(\<forall>f\<le>F. (p \<sqinter> pa) \<^emph>\<and> f \<le> (p \<^emph>\<and> any_shared f) \<sqinter> pa) \<longleftrightarrow>
    ((p \<sqinter> pa) \<^emph>\<and> F \<le> (p \<^emph>\<and> F) \<sqinter> pa)\<close>
  by (simp add: le_fun_def any_shared_def sepconj_conj_def, fast)

lemma rgsat_assert2:
  assumes
    \<open>(p \<sqinter> pa) \<^emph>\<and> F \<le> pa\<close>
    \<open>rel_image snd (rel_liftL ((p \<sqinter> pa) \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>sswa R (p \<sqinter> pa) \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { wssa R (p \<sqinter> pa) } Assert pa { sswa R (p \<sqinter> pa) }\<close>
  using assms
  by (blast intro: rgsat_assert)

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
  \<open>p \<^bold>\<mapsto> x \<equiv> \<lambda>h. h p = Some x \<and> (\<forall>p'. p' \<noteq> p \<longrightarrow> h p' = None)\<close>

definition points_to_upcl :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<^sup>\<Up>\<close> 90) where
  \<open>p \<^bold>\<mapsto>\<^sup>\<Up> x \<equiv> \<lambda>h. h p = Some x\<close>

definition points_to_perm
  :: \<open>'pt \<Rightarrow> 'perm \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> ('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> 's \<Rightarrow> bool\<close>
  (\<open>_ \<^bold>\<mapsto>\<^bsub>_\<^esub> _\<close> [90,0,90] 90)
  where
  \<open>pt \<^bold>\<mapsto>\<^bsub>perm\<^esub> e \<equiv> \<lambda>(ls,ss). (=) [pt \<mapsto> (Discr (e ss), perm)] ls\<close>

lemma points_to_upcl_eq:
  fixes x :: \<open>'a :: perm_alg\<close>
  assumes maxsep_x: \<open>\<forall>x'. \<not> x ## x'\<close>
  shows \<open>pt \<^bold>\<mapsto>\<^sup>\<Up> x = \<top> \<^emph> pt \<^bold>\<mapsto> x\<close>
  unfolding sepconj_def points_to_def points_to_upcl_def
  apply (clarsimp simp add: fun_eq_iff)
  apply (rename_tac h)
  apply (intro iffI)
   apply (rule_tac x=\<open>h(pt := None)\<close> in exI)
   apply (rule_tac x=\<open>[pt \<mapsto> x]\<close> in exI)
   apply force
  apply (clarsimp simp add: disjoint_option_def split: option.splits)
  apply (clarsimp simp add: plus_option_iff)
  apply (metis disjoint_fun_def disjoint_option_iff(1) disjoint_sym_iff maxsep_x)
  done

definition \<open>maximal_heap h \<equiv> \<forall>pt. h pt \<noteq> None\<close>

abbreviation \<open>heap_pred p \<equiv> (p \<times>\<^sub>P \<top>) \<circ> ppABC_to_ppACB\<close>


section \<open> Heap Commands \<close>

subsection \<open> Heap Read \<close>

definition heap_read_rel
  :: \<open>'x \<Rightarrow> 'pt \<Rightarrow> (
        (('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> fail_st) \<times> ('x \<Rightarrow> 'v) \<Rightarrow>
        (('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> fail_st) \<times> ('x \<Rightarrow> 'v) \<Rightarrow>
        bool)\<close>
  where
    \<open>heap_read_rel x pt \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        (\<exists>v \<pi>. l pt = Some (v, \<pi>) \<and> l' = l \<and> s' = s(x := the_discr v) \<and> fl' = Running) \<or>
        (l pt = None \<or> fl = Failed) \<and> l' = l \<and> s' = s \<and> fl' = Failed\<close>

abbreviation \<open>HeapRead x pt \<equiv> \<langle> heap_read_rel x pt \<rangle>\<close>
lemmas HeapRead_def = heap_read_rel_def


lemma rgsat_heap_read:
  fixes p :: \<open>('x \<Rightarrow> 'v) \<Rightarrow> bool\<close>
    and x v R \<pi> pt
  defines \<open>heap_read_guar \<equiv> (\<lambda>s s'. s' = s(x := v))\<close>
  and \<open>precond \<equiv> pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (\<lambda>_. v) \<sqinter> wssa R (\<S> (\<lambda>s. p (s(x := v))))\<close>
  and \<open>postcond \<equiv> pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (\<lambda>_. v) \<sqinter> sswa R (\<S> p)\<close>
assumes
    \<open>heap_read_guar \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } HeapRead x pt { postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  show \<open>nofailure_pred precond \<le> wssa R (nofailure_pred precond)\<close>
    unfolding precond_def
    by (clarsimp simp add: wlp_def points_to_perm_def, meson rtranclp_trans)
  then show \<open>sswa R (nofailure_pred precond) \<le> nofailure_pred I\<close>
    using assms(5)
    by (meson order_trans subpred_pred_times_eq_res_ppABC_to_ppACB_iff wlp_weaker_iff_sp_stronger)

  show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    by (clarsimp simp add: sp_def points_to_perm_def, meson rtranclp_trans)
  then show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred I\<close>
    using assms(6)
    by (meson order_trans subpred_pred_times_eq_res_ppABC_to_ppACB_iff wlp_weaker_iff_sp_stronger)

  show
    \<open>\<forall>f\<le>nofailure_pred F. sp (heap_read_rel x pt) (nofailure_pred precond \<^emph>\<and> f) \<le>
      nofailure_pred postcond \<^emph>\<and> any_shared f\<close>
    unfolding any_shared_def precond_def postcond_def
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise)
    apply (clarsimp simp add: sp_def points_to_perm_def sepconj_conj_def heap_read_rel_def)
    apply (clarsimp simp add: plus_option_def split: option.splits)
     apply (metis (mono_tags) comp_apply not_dom_then_singleton_plus_heap_eq wssa_trivial
        rtranclp.rtrancl_refl snd_conv)
    apply (metis (mono_tags) comp_apply rtranclp.rtrancl_refl snd_conv wssa_trivial)
    done

  show \<open>rel_image snd (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> heap_read_rel x pt)
          \<le> G\<close>
    using assms(4)
    unfolding heap_read_guar_def precond_def
    by (force simp add: heap_read_rel_def sepconj_conj_def plus_option_iff points_to_perm_def)
qed simp+


subsection \<open> Heap Write \<close>

definition heap_write_rel
  :: \<open>'pt \<Rightarrow> ('s \<Rightarrow> 'v) \<Rightarrow> ((('pt \<rightharpoonup> 'v discr \<times> 'perm) \<times> fail_st) \<times> 's) \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>heap_write_rel pt e \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        s' = s \<and> (
          (\<exists>v perm. l pt = Some (v, perm) \<and> fl = Running \<and> l' = l(pt \<mapsto> (Discr (e s), perm)) \<and> fl' = Running) \<or>
          (l pt = None \<or> fl = Failed) \<and> l' = l \<and> fl' = Failed)\<close>

abbreviation \<open>HeapWrite pt e \<equiv> \<langle> heap_write_rel pt e \<rangle>\<close>


lemma heap_write_rel_nofailure_rel_eq:
  \<open>sp (heap_write_rel pt e) (nofailure_pred p) =
    nofailure_pred (
      sp
        (\<lambda>(l,s) (l',s'). s' = s \<and> (\<exists>v perm. l pt = Some (v, perm) \<and> l' = l(pt \<mapsto> (Discr (e s), perm))))
        p)
    \<squnion> failure_pred ((\<lambda>(l',s'). l' pt = None) \<sqinter> p)\<close>
  apply (clarsimp simp add: heap_write_rel_def sp_def fun_eq_iff split: prod.splits)
  apply (case_tac b, force)
  apply clarsimp
  apply (metis (no_types, lifting) ext)
  done

lemma rgsat_pointer_write:
  fixes e pt p R \<pi> v
  defines \<open>precond \<equiv> (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> (\<lambda>_. v)) \<sqinter> wssa R (\<S> p)\<close>
    and \<open>postcond \<equiv> sswa R (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> e \<sqinter> \<S> p)\<close>
  assumes
    \<comment> \<open> this is the side condition that constrains permissions to be exclusive \<close>
    \<open>F \<le> - \<L> (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x')\<close>
    \<open>(=) \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } HeapWrite pt e { postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  show \<open>nofailure_pred precond \<le> wssa R (nofailure_pred precond)\<close>
    unfolding precond_def
    by (clarsimp simp add: points_to_perm_def wlp_def, meson rtranclp_trans)
  then show \<open>sswa R (nofailure_pred precond) \<le> nofailure_pred I\<close>
    by (meson assms(5) nofailure_pred_strong_mono order_trans wlp_weaker_iff_sp_stronger)

  show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    by (clarsimp simp add: points_to_perm_def sp_def, metis rtranclp_trans)
  then show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred I\<close>
    using assms(6) by fastforce

  have failure_helper: \<open>\<And>f. failure_pred ((\<lambda>(l', s'). l' pt = None) \<sqinter> (precond \<^emph>\<and> f)) = \<bottom>\<close>
    by (clarsimp simp add: fun_eq_iff precond_def points_to_perm_def sepconj_conj_def
        plus_option_iff, blast)

  let ?ra = \<open>(\<lambda>(l, s) (l', s'). s' = s \<and> (\<exists>v perm. l pt = Some (v, perm) \<and> l' = l(pt \<mapsto> (Discr (e s), perm))))\<close>
  let ?frame2 =
    \<open>\<forall>f\<le>F. sp ?ra (precond \<^emph>\<and> f) \<le> postcond \<^emph>\<and> any_shared f\<close>
  let ?frame1 =
    \<open>\<forall>f\<le>nofailure_pred F.
      sp (heap_write_rel pt e) (nofailure_pred precond \<^emph>\<and> f) \<le>
        nofailure_pred postcond \<^emph>\<and> any_shared f\<close>

  have \<open>\<top> = ?frame2\<close>
    using assms(3)
    unfolding precond_def postcond_def
    apply (clarsimp simp add: sp_def le_fun_def points_to_perm_def points_to_upcl_def
        sepconj_conj_def plus_option_iff)
    apply (elim disjE)
      (* None case *)
     apply clarsimp
     apply (rename_tac s l)
     apply (rule_tac x=\<open>[pt \<mapsto> (Discr (e s), \<pi>)]\<close> in exI)
     apply (rule_tac x=l in exI)
     apply (intro conjI)
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
      (* Some case, prevented by frame exclusivity *)
    apply clarsimp
    apply (rename_tac ss ls fs v' \<pi>')
    apply (subgoal_tac \<open>v' = Discr v\<close>)
     prefer 2
     apply (simp add: disjoint_fun_def disjoint_option_def split: option.splits)
     apply metis
    apply (subgoal_tac \<open>\<pi> ## \<pi>'\<close>)
     prefer 2
     apply clarsimp
     apply (metis disjoint_fun_def disjoint_option_simps(1) disjoint_prod_def fun_upd_same snd_conv)
    apply blast
    done
  also have \<open>... = ?frame1\<close>
    by (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise failure_helper
        nofailure_pred_sepconj_conj_distrib[symmetric] heap_write_rel_nofailure_rel_eq
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib)
  finally show ?frame1
    by simp

  show
    \<open>rel_image snd (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> heap_write_rel pt e) \<le>
      G\<close>
    using assms(4)
    by (clarsimp simp add: heap_write_rel_def nofailure_pred_sepconj_conj_distrib[symmetric]
        le_fun_def)
qed simp+

lemma top_write_frame_cond_iff_all_disjoint_perm:
  \<open>\<top> \<le> - \<L> (\<Squnion>x'\<in>Collect ((##) (Discr v, \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x') \<longleftrightarrow> (\<forall>\<pi>'. \<not> \<pi> ## \<pi>')\<close>
  by (force simp add: points_to_upcl_def le_fun_def)


subsection \<open> Heap Alloc \<close>

definition heap_alloc_rel
  :: \<open>('s \<Rightarrow> 'v) \<Rightarrow> ((('pt \<rightharpoonup> 'v discr \<times> 'perm::pre_perm_alg) \<times> fail_st) \<times> 's) \<Rightarrow> _ \<Rightarrow> bool\<close>
  where
    \<open>heap_alloc_rel e \<equiv>
      \<lambda>((l,fl),s) ((l',fl'),s').
        s' = s \<and> (
          (\<exists>pt \<pi>. l pt = None \<and> (\<forall>\<pi>'. \<not> \<pi> ## \<pi>') \<and> l' = l(pt \<mapsto> (Discr (e s), \<pi>))) \<and>
            fl = Running \<and> fl' = fl \<or>
          (fl = Failed \<or> (\<forall>pt. l pt \<noteq> None) \<or> (\<forall>\<pi>::'perm. \<exists>\<pi>'. \<pi> ## \<pi>')) \<and> l' = l \<and> fl' = Failed
      )\<close>

abbreviation \<open>HeapAlloc e \<equiv> \<langle> heap_alloc_rel e \<rangle>\<close>


lemma rgsat_pointer_alloc:
  fixes p pt e R
  defines \<open>precond \<equiv> \<L> emp \<sqinter> wssa R (\<S> p)\<close>
  \<comment> \<open> we obtain a is \<^emph>\<open>some\<close> totally disjoint permission \<close>
  and \<open>postcond \<equiv> (\<Squnion>pt. \<Squnion>\<pi>1\<in>{\<pi>1::'perm::pre_perm_alg. \<forall>\<pi>. \<not> \<pi>1 ## \<pi>}. sswa R (pt \<^bold>\<mapsto>\<^bsub>\<pi>1\<^esub> e \<sqinter> \<S> p))\<close>
  assumes
    \<open>(=) \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_not_maximal_heap: \<open>F \<le> - (\<L> maximal_heap)\<close>
    and maximal_perm_ex: \<open>\<exists>\<pi>::'perm. \<forall>\<pi>'. \<not> \<pi> ## \<pi>'\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } HeapAlloc e { postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  show \<open>nofailure_pred precond \<le> wssa R (nofailure_pred precond)\<close>
    unfolding precond_def
    by (clarsimp simp add: wlp_def emp_def, meson rtranclp_trans)
  then show \<open>sswa R (nofailure_pred precond) \<le> nofailure_pred I\<close>
    using assms(4)
    by (meson nofailure_pred_strong_mono order.trans wlp_weaker_iff_sp_stronger)

  show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    by (clarsimp simp add: points_to_perm_def sp_def heap_upd_eq_iff, metis rtranclp_trans)
  then show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred I\<close>
    using assms(5) nofailure_pred_strong_mono by blast

  show \<open>\<forall>f\<le>nofailure_pred F. sp (heap_alloc_rel e) (nofailure_pred precond \<^emph>\<and> f) \<le> nofailure_pred postcond \<^emph>\<and> any_shared f\<close>
    unfolding precond_def postcond_def
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib)
    apply (clarsimp simp add: heap_alloc_rel_def sp_def wlp_def emp_def le_fun_def sepconj_conj_def)
    apply (rename_tac ls fl ss fs)
    apply (elim disjE conjE)
      apply (clarsimp simp add: points_to_perm_def)
      apply (simp add: ex_simps[symmetric] del: ex_simps)
      apply (rule_tac x=fs in exI)
      apply (rule_tac x=ss in exI)
      apply (rule_tac x=pt in exI)
      apply (rule_tac x=\<pi> in exI)
      apply (rule_tac x=ss in exI)
      apply force
      (* contradiction between maximal frame and no maximal frame assumption. *)
     apply (cut_tac frame_not_maximal_heap)
     apply (clarsimp simp add: Sup_fun_def sepconj_conj_def ex_simps(1-4)[symmetric]
        emp_def le_fun_def maximal_heap_def simp del: ex_simps(1-4))
     apply (metis not_Some_prod_eq)
      (* contradiction between no maximal perm and maximal_perm_ex assumption. *)
    apply (cut_tac maximal_perm_ex)
    apply force
    done

  show \<open>rel_image snd (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> heap_alloc_rel e) \<le> G\<close>
    using assms(3)
    by (fastforce simp add: heap_alloc_rel_def)
qed simp+


subsection \<open> Heap Free \<close>

definition heap_free_rel
  :: \<open>'pt \<Rightarrow> ((('pt \<rightharpoonup> 'v discr \<times> 'perm::pre_perm_alg) \<times> fail_st) \<times> 's) \<Rightarrow> _ \<Rightarrow> bool\<close>
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
  defines \<open>precond \<equiv> wssa R (pt \<^bold>\<mapsto>\<^bsub>\<pi>\<^esub> e \<sqinter> \<S> p)\<close>
    and \<open>postcond \<equiv> \<L> emp \<sqinter> sswa R (\<S> p)\<close>
  assumes
    \<open>(=) \<le> G\<close>
    \<open>precond \<le> I\<close>
    \<open>postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frames_disjoint_at_pt:
    \<open>F \<le> - \<L>\<^sub>S (\<lambda>ss. (\<Squnion>x'\<in>Collect ((##) (Discr (e ss), \<pi>)). pt \<^bold>\<mapsto>\<^sup>\<Up> x'))\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f { precond } HeapFree pt { postcond }\<close>
  using assms
proof (intro rgsat_atom[where p=\<open>nofailure_pred precond\<close> and q=\<open>nofailure_pred postcond\<close>])
  show \<open>nofailure_pred precond \<le> wssa R (nofailure_pred precond)\<close>
    unfolding precond_def
    by (clarsimp simp add: wlp_def, metis rtranclp_trans)
  then show \<open>sswa R (nofailure_pred precond) \<le> nofailure_pred I\<close>
    using assms(4)
    by (meson nofailure_pred_strong_mono order.trans wlp_weaker_iff_sp_stronger)

  show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred postcond\<close>
    unfolding postcond_def
    by (clarsimp simp add: points_to_perm_def  emp_def sp_def heap_upd_eq_iff, metis rtranclp_trans)
  then show \<open>sswa R (nofailure_pred postcond) \<le> nofailure_pred I\<close>
    using assms(5) nofailure_pred_strong_mono by blast

  show \<open>\<forall>f\<le>nofailure_pred F.
          sp (heap_free_rel pt) (nofailure_pred precond \<^emph>\<and> f) \<le>
            nofailure_pred postcond \<^emph>\<and> any_shared f\<close>
    unfolding precond_def postcond_def heap_free_rel_def emp_def
    apply (simp add: all_subpred_pred_times_eq_res_ppABC_to_ppACB_internalise
        nofailure_pred_sepconj_conj_distrib[symmetric]
        any_shared_pred_times_eq_res_ppABC_to_ppACB_distrib)
    apply (clarsimp simp add: sp_def wlp_def points_to_perm_def sepconj_conj_def plus_option_iff)
    apply (rename_tac lfs fl ss ls fs)
      \<comment> \<open> Replacing \<open>x\<close> with \<open>(e ss)\<close> here causes simplifier loops. Presumably because
            the stabilised predicate we are deriving this from can now show many \<open>e ss = e ss'\<close>
            lemmas. \<close>
    apply (subgoal_tac \<open>\<exists>x. ls = [pt \<mapsto> (Discr x, \<pi>)]\<close>)
     prefer 2
     apply force
    apply clarsimp
    apply (rule conjI, force)
    apply (elim disjE)
     apply clarsimp
     apply (metis fun_upd_triv)
      (* find a contradiction with the disjoint frame assm *)
    apply (cut_tac frames_disjoint_at_pt)
    apply (clarsimp simp add: disjoint_fun_def disjoint_option_def points_to_upcl_def le_fun_def
        split: if_splits)
    apply (metis (mono_tags, lifting) fst_conv heap_upd_eq_iff rtranclp.rtrancl_refl)
    done

  show \<open>rel_image snd (rel_liftL (nofailure_pred precond \<^emph>\<and> nofailure_pred F) \<sqinter> heap_free_rel pt) \<le> G\<close>
    using assms(3)
    by (fastforce simp add: heap_free_rel_def)
qed simp+


end