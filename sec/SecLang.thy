theory SecLang
  imports SecLogic
begin

section \<open> Helpers \<close>

text \<open> TODO: move \<close>

lemma implication_then_inf_neg_false:
  fixes p q :: \<open>'a :: boolean_algebra\<close>
  shows \<open>p \<le> q \<Longrightarrow> p \<sqinter> - q = \<bottom>\<close>
  by (simp add: inf_shunt)

lemma any_shared_pred_times_top_eq[simp]:
  \<open>any_shared (p \<times>\<^sub>P \<top>) = p \<times>\<^sub>P \<top>\<close>
  by (fastforce simp add: any_shared_def)

lemma sepconj_conj_unit_right[simp]:
  fixes p  :: \<open>'l::multiunit_sep_alg \<times> 's \<Rightarrow> bool\<close>
  shows \<open>p \<^emph>\<and> (emp \<times>\<^sub>P \<top>) = p\<close>
  by (clarsimp simp add: sepconj_conj_def emp_def fun_eq_iff)
    (metis sepadd_unit_right unitof_disjoint2 unitof_is_sepadd_unit)

lemma sepconj_conj_unit_left[simp]:
  fixes p  :: \<open>'l::multiunit_sep_alg \<times> 's \<Rightarrow> bool\<close>
  shows \<open>(emp \<times>\<^sub>P \<top>) \<^emph>\<and> p = p\<close>
  by (clarsimp simp add: sepconj_conj_def emp_def fun_eq_iff)
    (metis sepadd_unit_def unitof_disjoint unitof_is_sepadd_unit)

lemma conj_eqpred_neq_simp[simp]:
  \<open>x \<noteq> y \<Longrightarrow> (=) x \<sqinter> (=) y = \<bottom>\<close>
  by (simp add: fun_eq_iff)


section \<open> Healthiness Predicate Transformers \<close>


section \<open> Predicate-lifting Await \<close>

text \<open> Predicate-lifting await is always quasirefl preserving \<close>

lemma quasirefl_states_await:
  \<open>quasirefl_preserv (await_rel p) = quasireflcl_states p\<close>
  by (simp add: await_rel_def quasirefl_preserv_eq quasireflcl_states_eq)

lemma quasirefl_states_exch4_await:
  \<open>quasirefl_preserv\<^sub>\<ddagger> (await_rel p) = quasireflcl_states\<^sub>\<ddagger> p\<close>
  by (simp add: quasirefl_preserv_exch4_eq await_rel_def quasireflcl_states_exch4_eq fun_eq_iff)


text \<open> and symmetry preserving. \<close>

lemma sym_preserv_await:
  \<open>sym_preserv (await_rel p) = symcl_states p\<close>
  by (force simp add: await_rel_def sym_preserv_eq symcl_states_eq fun_eq_iff)

lemma sym_preserv_exch4_await:
  \<open>sym_preserv\<^sub>\<ddagger> (await_rel p) = symcl_states\<^sub>\<ddagger> p\<close>
  by (force simp add: await_rel_def sym_preserv_exch4_eq symcl_states_exch4_eq
      fun_eq_iff sym_preserv_eq symcl_states_eq)


section \<open> Pretty double-failure \<close>

definition
  \<open>doublefl_rel rfl r \<equiv> \<lambda>(((lx,flx), (ly,fly)), s) (((lx',flx'), (ly',fly')), s').
    r ((lx,ly), s) ((lx',ly'), s') \<and> rfl (flx,fly) (flx',fly')\<close>

lemma doublefl_rel_apply[simp]:
  \<open>doublefl_rel rfl r (((lx,flx), (ly,fly)), s) (((lx',flx'), (ly',fly')), s') \<longleftrightarrow>
    r ((lx,ly), s) ((lx',ly'), s') \<and> rfl (flx,fly) (flx',fly')\<close>
  by (clarsimp simp add: doublefl_rel_def)

lemma doublefl_rel_bot_eq[simp]:
  \<open>doublefl_rel \<bottom> = \<bottom>\<close>
  \<open>doublefl_rel rfl \<bottom> = \<bottom>\<close>
  by (clarsimp simp add: doublefl_rel_def fun_eq_iff)+


definition \<open>doublefl_pred rfl p \<equiv> \<lambda>(((lx,flx), (ly,fly)), s). p ((lx,ly), s) \<and> rfl (flx,fly)\<close>

abbreviation \<open>doublefl_val_pred flx fly \<equiv> doublefl_pred \<lblot> (=) flx \<bar> (=) fly \<rblot>\<close>
abbreviation \<open>running2_pred \<equiv> doublefl_pred \<lblot> (=) Running \<rblot>\<close>
abbreviation \<open>failed2_pred \<equiv> doublefl_pred \<lblot> (=) Failed \<rblot>\<close>

lemma doublefl_val_pred_def:
  \<open>doublefl_val_pred flx fly p =
    (\<lambda>(((lx, flxx), ly, flyy), s). p ((lx, ly), s) \<and> flxx = flx \<and> flyy = fly)\<close>
  by (force simp add: doublefl_pred_def)

lemmas running2_pred_def = doublefl_val_pred_def[of Running Running]
lemmas failed2_pred_def = doublefl_val_pred_def[of Failed Failed]

lemma doublefl_pred_apply[simp]:
  \<open>doublefl_pred r p (((a, x'), (b, y')), s) = (r (x',y') \<and> p ((a, b), s))\<close>
  by (force simp add: doublefl_pred_def)

lemma doublefl_pred_flbot_eq[simp]:
  \<open>doublefl_pred \<bottom> p = \<bottom>\<close>
  by (force simp add: doublefl_pred_def)

lemma doublefl_pred_conj_merge[simp]:
  \<open>doublefl_pred ra pa \<sqinter> doublefl_pred rb pb = doublefl_pred (ra \<sqinter> rb) (pa \<sqinter> pb)\<close>
  by (force simp add: doublefl_pred_def)


lemma wssa_doublefl_pred_distrib:
  \<open>wssa R (doublefl_pred flr p) = doublefl_pred flr (wssa R p)\<close>
  by (force simp add: doublefl_pred_def wlp_def)

lemma sswa_doublefl_pred_distrib:
  \<open>sswa R (doublefl_pred flr p) = doublefl_pred flr (sswa R p)\<close>
  by (force simp add: doublefl_pred_def sp_def)

lemma any_shared_doublefl_pred_distrib:
  \<open>any_shared (doublefl_pred flr p) = doublefl_pred flr (any_shared p)\<close>
  by (force simp add: doublefl_pred_def)

lemma doublefl_pred_mono:
  \<open>flr \<noteq> \<bottom> \<Longrightarrow> doublefl_pred flr p \<le> doublefl_pred flr q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: doublefl_pred_def) fast

lemma doublefl_val_pred_mono[simp]:
  \<open>doublefl_val_pred x y p \<le> doublefl_val_pred x y q \<longleftrightarrow> p \<le> q\<close>
  by (simp add: doublefl_pred_def) fast


lemma le_doublefl_val_pred_iff:
  \<open>p \<le> doublefl_val_pred x y q \<longleftrightarrow> (\<exists>q'. q' \<le> q \<and> p = doublefl_val_pred x y q')\<close>
  apply (clarsimp simp add: le_fun_def fun_eq_iff doublefl_pred_def invrel_def)
  apply (rule iffI)
   apply (rule_tac x=\<open>\<lambda>((lsx, lsy), ss). p (((lsx, x), (lsy, y)), ss)\<close> in exI, force)
  apply force
  done

lemma All_doublefl_val_pred_internalise:
  \<open>(\<forall>p\<le>doublefl_val_pred x y P. \<Q> p) \<longleftrightarrow>
    (\<forall>p\<le>P. \<Q> (doublefl_val_pred x y p))\<close>
  by (simp add: le_doublefl_val_pred_iff) blast


lemma doublefl_val_pred_sepconj_conj_distrib:
  fixes x :: fail_st
  shows \<open>doublefl_val_pred x x p \<^emph>\<and> doublefl_val_pred x x q = doublefl_val_pred x x (p \<^emph>\<and> q)\<close>
  by (cases x)
    (clarsimp simp add: doublefl_val_pred_def sepconj_conj_apply fun_eq_iff, blast)+

lemma failure2_implies_running2_iff[simp]:
  \<open>failed2_pred p \<le> running2_pred q \<longleftrightarrow> \<top> \<le> - p\<close>
  by (simp add: failed2_pred_def running2_pred_def le_fun_def all_fail_st_eq)


abbreviation ff_rgsat_pretty
  (\<open>_, _, _, _, _ \<turnstile>\<^sub>f\<^sub>f { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>R, G, I, F, T \<turnstile>\<^sub>f\<^sub>f { p } c { q } \<equiv>
    rgsat c R G
      (running2_pred p) (running2_pred q)
      (running2_pred I) (running2_pred F)
      T\<close>

lemmas ff_rgsat_weaken =
  rgsat_weaken[where
    p'=\<open>running2_pred p'\<close> and q'=\<open>running2_pred q'\<close> and
    I'=\<open>running2_pred I'\<close> and F'=\<open>running2_pred F'\<close> and
    p=\<open>running2_pred p\<close> and q=\<open>running2_pred q\<close> and
    I=\<open>running2_pred I\<close> and F=\<open>running2_pred F\<close> for p q I F p' q' I' F', simplified]


section \<open> Relational Assertion \<close>

definition relassert_rel
  :: \<open>(('l, 's) rgsep_secstate \<Rightarrow> bool) \<Rightarrow>
      (('l \<times> fail_st, 's) rgsep_secstate \<Rightarrow> ('l \<times> fail_st, 's) rgsep_secstate \<Rightarrow> bool)\<close>
  where
  \<open>relassert_rel p \<equiv>
    \<lambda>(((lx,flx), (ly,fly)), s) (((lx',flx'), (ly',fly')), s').
      lx' = lx \<and> ly' = ly \<and> s' = s \<and>
        ((p ((lx,ly),s) \<or> flx = Failed \<or> fly = Failed) \<and> flx' = flx \<and> fly' = fly \<or>
          flx = Running \<and> fly = Running \<and> \<not> p ((lx,ly), s) \<and> flx' = Failed \<and> fly' = Failed)\<close>

abbreviation RelAssert
  :: \<open>(('l, 's) rgsep_secstate \<Rightarrow> bool) \<Rightarrow> ('l \<times> fail_st, 's) rgsep_secstate comm\<close>
  where
    \<open>RelAssert p \<equiv> \<langle> relassert_rel p \<rangle>\<close>


subsubsection \<open> Healthiness Properties \<close>

text \<open> Relassert is quasi-reflexivity preserving when TODO \<close>
lemma relassert_quasireflp_steprel:
  fixes p :: \<open>('a, 'b) rgsep_secstate \<Rightarrow> bool\<close>
  shows
    \<open>quasirefl_preserv\<^sub>\<ddagger> (relassert_rel p) =
        doublefl_val_pred Running Running (quasireflcl_states\<^sub>\<ddagger> p \<sqinter> quasireflcl_states\<^sub>\<ddagger> (- p)) \<squnion>
        doublefl_val_pred Running Failed (p \<circ> \<ddagger> \<circ> \<Delta> \<circ> fst \<circ> \<ddagger>) \<squnion>
        doublefl_val_pred Failed Running (p \<circ> \<ddagger> \<circ> \<Delta> \<circ> snd \<circ> \<ddagger>) \<squnion>
        failed2_pred \<top>\<close>
  by (clarsimp simp add: relassert_rel_def quasirefl_preserv_exch4_eq quasireflcl_states_exch4_eq
      fun_eq_iff all_fail_st_eq all_conj_distrib)

text \<open> It is symmetry preserving when TODO \<close>

lemma relassert_sym_preserv_eq:
  \<open>sym_preserv\<^sub>\<ddagger> (relassert_rel p) =
    running2_pred (symcl_states\<^sub>\<ddagger> p) \<squnion> doublefl_pred (- \<lblot> (=) Running \<rblot>) \<top>\<close>
  by (clarsimp simp add: relassert_rel_def sym_preserv_exch4_eq symp_def
      fun_eq_iff all_fail_st_eq all_conj_distrib symcl_states_exch4_eq)
    fast


subsection \<open> Output \<close>

definition output_rel
  :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow>
        (('l \<times> fail_st, 's) rgsep_secstate \<Rightarrow> ('l \<times> fail_st, 's) rgsep_secstate \<Rightarrow> bool)\<close>
  where
    \<open>output_rel h \<equiv> relassert_rel (\<bbbA>\<^sub>\<ddagger> h)\<close>

lemmas output_rel_def2 =
  output_rel_def[simplified relassert_rel_def]

abbreviation \<open>Output h \<equiv> \<langle> output_rel h \<rangle>\<close>


subsubsection \<open> Healthiness Properties \<close>

text \<open> Output is quasirefl preserving when agreement holds, or the state has failed \<close>
lemma output_quasireflp_steprel_running:
  fixes p :: \<open>('a, 'b) rgsep_secstate \<Rightarrow> bool\<close>
  shows
    \<open>quasirefl_preserv\<^sub>\<ddagger> (output_rel f) =
      running2_pred (\<bbbA>\<^sub>\<ddagger> f) \<squnion> doublefl_pred (- \<lblot> (=) Running \<rblot>) \<top>\<close>
  apply (simp add: output_rel_def relassert_quasireflp_steprel inf_sup_distrib2 predrel_inf_merge
      comp_def sec_agree_def)
  apply (simp add: fun_eq_iff all_fail_st_eq)
  done

text \<open> It is symmetry preserving always \<close>

lemma output_sym_preserv_eq[simp]:
  \<open>sym_preserv\<^sub>\<ddagger> (output_rel p) = \<top>\<close>
  by (simp add: output_rel_def relassert_sym_preserv_eq inf_sup_distrib2 predrel_inf_merge
      comp_def sec_agree_def doublefl_pred_def fun_eq_iff)


subsubsection \<open> Misc Lemmas \<close>

lemma sp_output_rel_running2_pred_eq:
  \<open>sp (output_rel h) (running2_pred p) = running2_pred (\<bbbA>\<^sub>\<ddagger> h \<sqinter> p) \<squnion> failed2_pred (- \<bbbA>\<^sub>\<ddagger> h \<sqinter> p)\<close>
  by (force split: prod.splits simp add: sp_def output_rel_def2 fun_eq_iff conj_disj_distribR
      running2_pred_def failed2_pred_def)

lemma pretest_running2_pred_inf_relassert_rel_eq:
  \<open>pretest (running2_pred p) \<sqinter> relassert_rel p' =
    pretest (running2_pred (p \<sqinter> p')) \<sqinter> (=) \<squnion>
    doublefl_rel (predrel \<lblot> (=) Running \<rblot> \<lblot> (=) Failed \<rblot>) ((=) \<sqinter> pretest (p \<sqinter> -p'))\<close>
  by (simp add: running2_pred_def relassert_rel_def fun_eq_iff all_fail_st_eq) fast


subsubsection \<open> Output Rule \<close>

lemma rgsat_output:
  assumes main:
    \<open>wssa R p \<^emph>\<and> F \<le> \<bbbA>\<^sub>\<ddagger> h\<close>
    \<open>rel_image snd (pretest (wssa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    \<open>wssa R p \<le> I\<close>
    and misc:
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile>\<^sub>f\<^sub>f { wssa R p } Output h { wssa R p }\<close>
  using misc
proof (intro rgsat_atom[where p=\<open>running2_pred p\<close> and q=\<open>running2_pred (wssa R p)\<close>])
  show \<open>running2_pred (wssa R p) \<le> wssa R (running2_pred p)\<close>
    by (simp add: wssa_doublefl_pred_distrib)
  show \<open>sswa R (running2_pred (wssa R p)) \<le> running2_pred (wssa R p)\<close>
    by (simp add: sswa_doublefl_pred_distrib)

  show \<open>\<forall>f\<le>running2_pred F.
       sp (output_rel h) (wssa R (running2_pred p) \<^emph>\<and> f) \<le> running2_pred (wssa R p) \<^emph>\<and> any_shared f\<close>
    using main(1)
    apply (simp add: All_doublefl_val_pred_internalise wssa_doublefl_pred_distrib
        doublefl_val_pred_sepconj_conj_distrib any_shared_doublefl_pred_distrib
        sp_output_rel_running2_pred_eq all_conj_distrib imp_conjR)
    apply (rule conjI)
     apply (meson order.refl le_doublefl_val_pred_iff le_infI2 self_implies_self_any_shared
        sepconj_conj_mono; fail)
    apply (simp add: shunt2[symmetric] atom_variant_compressed_frame(1))
    done
  show \<open>rel_image snd (pretest (wssa R (running2_pred p) \<^emph>\<and> running2_pred F) \<sqinter> output_rel h) \<le> G\<close>
    using main(1-2)
     apply (simp add: output_rel_def wssa_doublefl_pred_distrib
        doublefl_val_pred_sepconj_conj_distrib pretest_running2_pred_inf_relassert_rel_eq
        implication_then_inf_neg_false)
    apply (clarsimp simp add: le_fun_def)
    apply blast
    done

  show \<open>wssa R (running2_pred p) \<le> running2_pred I\<close>
    using main
    by (simp add: wssa_doublefl_pred_distrib)
  show \<open>sswa R (running2_pred (wssa R p)) \<le> running2_pred I\<close>
    using main
    by (simp add: sswa_doublefl_pred_distrib)
qed simp+


section \<open> Secure If-statement \<close>

\<comment> \<open> The program produced by \<open>liftC (IfThenElse p)\<close> \<close>
definition \<open>SecIfThenElse p ct cf \<equiv> Await (\<lblot> p \<rblot>) ;; ct \<^bold>\<box> Await (\<lblot> -p \<rblot>) ;; cf\<close>

lemma SecIfThenElse_inject[simp]:
  \<open>SecIfThenElse p1 ct1 cf1 = SecIfThenElse p2 ct2 cf2 \<longleftrightarrow> p1 = p2 \<and> ct1 = ct2 \<and> cf1 = cf2\<close>
  by (clarsimp simp add: SecIfThenElse_def await_rel_def fun_eq_iff) blast

lemma SecIfThenElse_distinct[simp]:
  \<open>SecIfThenElse p ct cf \<noteq> Skip\<close>
  \<open>SecIfThenElse p ct cf \<noteq> c1 ;; c2\<close>
  \<open>SecIfThenElse p ct cf \<noteq> c1 \<parallel> c2\<close>
  \<open>SecIfThenElse p ct cf \<noteq> \<langle>ar\<rangle>\<close>
  \<open>Skip \<noteq> SecIfThenElse p ct cf\<close>
  \<open>c1 ;; c2 \<noteq> SecIfThenElse p ct cf\<close>
  \<open>c1 \<parallel> c2 \<noteq> SecIfThenElse p ct cf\<close>
  \<open>\<langle>ar\<rangle> \<noteq> SecIfThenElse p ct cf\<close>
  by (simp add: SecIfThenElse_def)+

lemma gensep_rule_sec_if_then_else:
  assumes
    \<open>rel_image snd (pretest (sswa R p \<^emph>\<and> F) \<sqinter> (=)) \<le> G\<close>
    and tt_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> \<lblot> pa \<rblot> \<le> (sswa R p \<sqinter> \<lblot> pa \<rblot>) \<^emph>\<and> any_shared f\<close>
    and ff_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> \<lblot> -pa \<rblot> \<le> (sswa R p \<sqinter> \<lblot> -pa \<rblot>) \<^emph>\<and> any_shared f\<close> 
    and body_assms:
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) } ctt { q }\<close>
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) } cff { q }\<close>
    and misc_assms:
    \<open>T RGSepWeaken\<close>
    \<open>T RGSepAtom\<close>
    \<open>T RGSepEndet\<close>
    \<open>T RGSepSeq\<close>
    \<open>sswa R p \<le> I\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { p } SecIfThenElse pa ctt cff { q }\<close>
  using misc_assms
  unfolding SecIfThenElse_def
proof (intro rgsat_weaken_prepost[where p=p and p'=\<open>sswa R p\<close> and q=q and q'=q],
    intro rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
      where I=I and Ia=\<open>sswa R p \<squnion> I\<close> and Ib=\<open>sswa R p \<squnion> I\<close>])
  show \<open>R, G, sswa R p, F, T \<turnstile> { sswa R p } Await (\<lblot> pa \<rblot>) { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) }\<close>
    using misc_assms assms(1) tt_guard_frame_cond
    apply (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>sswa R p \<sqinter> \<lblot> pa \<rblot>\<close>])
          apply force
         apply force
        apply (simp add: inf_commute[of \<open>\<lblot> pa \<rblot>\<close>]; fail)
       apply (simp add: await_rel_def inf_left_commute le_infI2 rel_image_snd_galois; fail)
      apply force
     apply (metis order.refl inf_sup_aci(1) inf_sup_ord(2) wlp_weaker_iff_sp_stronger
        wssa_over_sswa_eq)
    apply force
    done
  show \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> pa \<rblot>) } ctt { q }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, T \<turnstile> { sswa R p } Await (\<lblot> -pa \<rblot>) { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) }\<close>
    using ff_guard_frame_cond misc_assms assms
    apply (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>sswa R p \<sqinter> \<lblot> -pa \<rblot>\<close>])
          apply force
         apply force
        apply (simp add: inf_commute[of \<open>\<lblot> - pa \<rblot>\<close>]; fail)
       apply (simp add: await_rel_def inf_left_commute le_infI2 rel_image_snd_galois; fail)
      apply force
     apply (metis order.refl inf_sup_aci(1) inf_sup_ord(2) wlp_weaker_iff_sp_stronger
        wssa_over_sswa_eq)
    apply force
    done
  show \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R p \<sqinter> \<lblot> -pa \<rblot>) } cff { q }\<close>
    using body_assms
    by blast
  show \<open>p \<le> sswa R p\<close>
    by blast
qed simp+


section \<open> Declassification \<close>

definition declassify_rel
  :: \<open>('l \<times> 's \<Rightarrow> 'v) \<Rightarrow> (('l, 's) rgsep_secstate \<Rightarrow> ('l, 's) rgsep_secstate \<Rightarrow> bool)\<close>
  where
    \<open>declassify_rel h \<equiv> await_rel (\<bbbA>\<^sub>\<ddagger> h)\<close>

lemmas declassify_rel_def2 =
  await_rel_def[where p=\<open>\<bbbA>\<^sub>\<ddagger> h\<close> for h, simplified declassify_rel_def[symmetric]]

abbreviation \<open>Declassify h \<equiv> \<langle> declassify_rel h \<rangle>\<close>


subsection \<open> Healthiness Properties \<close>

text \<open> Output is quasirefl preserving when agreement holds, or the state has failed \<close>
lemma declassify_quasireflp_steprel_eq:
  \<open>quasirefl_preserv\<^sub>\<ddagger> (declassify_rel f) = \<top>\<close>
  by (simp add: declassify_rel_def quasirefl_states_exch4_await)

text \<open> It is symmetry preserving always \<close>

lemma declassify_sym_preserv_eq[simp]:
  \<open>sym_preserv\<^sub>\<ddagger> (declassify_rel p) = \<top>\<close>
  by (simp add: declassify_rel_def sym_preserv_exch4_await)


subsection \<open> Declassify Rule \<close>

lemma rgsat_declassify:
  assumes
    \<open>\<forall>f\<le>F. (wssa R p \<^emph>\<and> f) \<sqinter> \<bbbA>\<^sub>\<ddagger> h \<le> (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<^emph>\<and> any_shared f\<close>
    \<open>rel_image snd (pretest ((wssa R p \<^emph>\<and> F) \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<sqinter> (=)) \<le> G\<close>
    \<open>wssa R p \<le> I\<close>
    \<open>sswa R (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<le> I\<close>
    \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { wssa R p } Declassify h { sswa R (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) }\<close>
  using assms(3-)
proof (intro rgsat_atom[OF order.refl order.refl])
  show \<open>\<forall>f\<le>F. sp (declassify_rel h) (wssa R p \<^emph>\<and> f) \<le> (p \<sqinter> \<bbbA>\<^sub>\<ddagger> h) \<^emph>\<and> any_shared f\<close>
    using assms(1)
    by (clarsimp simp add: sp_def declassify_rel_def) blast
  show \<open>rel_image snd (pretest (wssa R p \<^emph>\<and> F) \<sqinter> declassify_rel h) \<le> G\<close>
    using assms(2)
    by (force simp add: declassify_rel_def2)
qed simp+

lemma declassify_as_assume_helper:
  \<open>\<forall>f\<le>emp \<times>\<^sub>P \<top>. (\<top> \<^emph>\<and> f) \<sqinter> \<bbbA>\<^sub>\<ddagger> h \<le> \<bbbA>\<^sub>\<ddagger> h \<^emph>\<and> any_shared f\<close>
  apply (clarsimp simp add: le_fun_def emp_def sepconj_conj_def)
  apply (metis sepadd_unit_right)
  done

lemmas declassify_as_assume =
  rgsat_declassify[where R=\<open>(=)\<close> and p=\<open>\<top>\<close> and h=\<open>h :: ('l::multiunit_sep_alg \<times> 's) \<Rightarrow> bool\<close>
                    and I=\<open>\<top>\<close> and F=\<open>emp \<times>\<^sub>P \<top>\<close> for h, simplified, OF declassify_as_assume_helper]


subsection \<open> Healthiness of Commands \<close>

text \<open> With the exchanged definitions in hand, we can reason about \<close>

lemma same_state_nonrevealing_exch4_lift_rel_exch4:
  \<open>same_state_nonrevealing\<^sub>\<ddagger> (lift_rel_exch4 r)\<close>
  by (simp add: same_state_nonrevealing_exch4_eq nonrevealing_eq lift_rel_exch4_def le_fun_def)

lemma same_state_nonrevealing_exch4_declassify:
  \<open>same_state_nonrevealing\<^sub>\<ddagger> (declassify_rel h)\<close>
  by (simp add: same_state_nonrevealing_exch4_eq nonrevealing_eq declassify_rel_def2
      sec_agree_def le_fun_def)

lemma same_state_nonrevealing_exch4_output:
  \<open>same_state_nonrevealing\<^sub>\<ddagger> (output_rel h)\<close>
  by (simp add: same_state_nonrevealing_exch4_eq nonrevealing_eq output_rel_def2 le_fun_def)
    force

lemma nondeclassifying_exch4_lift_rel_exch4:
  \<open>nondeclassifying\<^sub>\<ddagger> (lift_rel_exch4 r) = \<top>\<close>
  by (simp add: nondeclassifying_exch4_eq fun_eq_iff)

lemma nondeclassifying_exch4_declassify:
  \<open>nondeclassifying\<^sub>\<ddagger> (declassify_rel f) = \<bbbA>\<^sub>\<ddagger> f\<close>
  by (simp add: declassify_rel_def2 nondeclassifying_exch4_eq unlift_pred_def pre_state_def
      sec_agree_exch4_eq fun_eq_iff)


end