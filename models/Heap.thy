theory Heap
  imports Failure Stack
begin


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


section \<open> Heap Predicates \<close>

definition points_to :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<mapsto>\<close> 90) where
  \<open>\varho \<^bold>\<mapsto> x \<equiv> (=) [p \<mapsto> x]\<close>

definition val_at_heap :: \<open>'a \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'v) \<Rightarrow> bool\<close> (\<open>\<^bold>@\<^sub>\<H>\<close>) where
  \<open>\<^bold>@\<^sub>\<H> pt p \<equiv> \<lambda>h. \<forall>v. h pt = Some v \<longrightarrow> p v\<close>


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
    and R \<pi> pt u2v F
  defines \<open>heap_read_G \<equiv> (\<lambda>ss ss'. \<exists>fs vf.
      F (fs, ss) \<and>
      (fs pt = None \<and> ss' = ss(x := u2v (e ss)) \<or>
        fs pt = Some vf \<and> ss' = ss(x := u2v (e ss + vf))) )\<close>
  defines\<open>precond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> ((\<lambda>ss. p (ss(x := u2v (e ss)))) \<sqinter> \<^bold>@ x ((=) X))\<close>
  defines \<open>postcond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e (ss(x := X))) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
  defines \<open>frame_post :: (('a \<rightharpoonup> 'v) \<times> ('x \<Rightarrow> 'u) \<Rightarrow> bool) \<equiv>
    \<lceil>\<lambda>ss. \<L> (\<^bold>@\<^sub>\<H> pt (\<lambda>vf. p (ss(x := u2v (e ss))) \<longrightarrow> p (ss(x := u2v (e ss + vf))) )) \<rceil>\<^sub>\<S>\<close>
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
     apply (force simp add: val_at_heap_def)
      (* \<Leftarrow> *)
    apply (rename_tac fs ss ls)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, fast)
    apply (subgoal_tac \<open>ls = [pt \<mapsto> e ss]\<close>)
     prefer 2
     apply (fastforce simp add: precond_def wlp_def points_to_def)
    apply (case_tac \<open>fs pt\<close>)
      (** \<open>fs pt = None\<close> *)
     apply (simp add: frame_post_def val_at_heap_def; fail)
      (** \<open>fs pt = Some ...\<close> *)
    apply (rename_tac vf)
    apply (drule_tac x=\<open>ls + fs\<close> and y=\<open>e ss + vf\<close> in spec2, drule mp, force)
    apply clarsimp
    apply (drule_tac x=\<open>[pt \<mapsto> e ss]\<close> in spec)
    apply (simp add: postcond_def frame_post_def)
    apply (clarsimp simp add: disjoint_sym_iff val_at_heap_def points_to_def fun_eq_iff
        plus_option_iff if_distrib[of \<open>\<lambda>x. x = _\<close>] if_distrib[of \<open>\<lambda>x. x + _ = _\<close>] if_bool_eq_conj
        all_conj_distrib eq_commute[of _ \<open>_ pt\<close>])
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
    apply (fastforce simp add: wssa_comp_ppABC_to_ppACB_distrib heap_read_rel_def sepconj_conj_def
        plus_option_iff ex_disj_distrib conj_disj_distribR wlp_def points_to_def val_at_def)
    done
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
  :: \<open>('a \<Rightarrow> 'u) \<Rightarrow> 'x \<Rightarrow> (('x \<Rightarrow> 'u) \<Rightarrow> 'v) \<Rightarrow>
        ((('a \<rightharpoonup> 'v) \<times> fail_st) \<times> ('x \<Rightarrow> 'u)) \<Rightarrow> _ \<Rightarrow> bool\<close>
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
  fixes R F x X
    and p :: \<open>('s \<Rightarrow> 'u) \<Rightarrow> bool\<close>
    and pt :: \<open>('s \<Rightarrow> 'u) \<Rightarrow> 'a\<close>
    and Ptr :: \<open>'a \<Rightarrow> 'u\<close>
    and the_ptr :: \<open>'u \<Rightarrow> 'a\<close>
    and e :: \<open>('s \<Rightarrow> 'u) \<Rightarrow> 'v::pre_perm_alg\<close>
  defines \<open>precond \<equiv> \<L> emp \<sqinter> \<S> (p \<sqinter> \<^bold>@ x ((=) X))\<close>
  defines
    \<open>postcond \<equiv>
      \<lceil> \<lambda>ss. \<L> (the_ptr (ss x) \<^bold>\<mapsto> e (ss(x := X))) \<rceil>\<^sub>\<S> \<sqinter> \<S> (\<lambda>ss. p (ss(x := X)))\<close>
  assumes
    \<open>(\<lambda>s s'. \<exists>pt. s' = s(x := Ptr pt)) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_cond: \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> \<L> (\<Squnion>pt. \<^bold>@\<^sub>\<H> pt \<bottom>)\<close>
    and the_ptr_Ptr_inv: \<open>\<And>a. the_ptr (Ptr a) = a\<close>
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
    \<open>(F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> \<L> (\<Squnion>pt. \<^bold>@\<^sub>\<H> pt \<bottom>)) =
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
     apply (clarsimp simp add: precond_def  plus_option_iff ex_disj_distrib wlp_def emp_def
        val_at_heap_def)
     apply (metis option.discI rtranclp.rtrancl_refl)
        (* \<Leftarrow> *)
    apply (drule spec, drule mp, fast)
    apply (clarsimp simp add: heap_alloc_rel_def all_conj_distrib precond_def wlp_def emp_def
        imp_ex_conjL imp_conjL val_at_heap_def)
    apply (metis disjoint_sym map_empty_plus(1) not_eq_None rtranclp.rtrancl_refl)
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
    apply (simp add: the_ptr_Ptr_inv) \<comment> \<open> do \<^emph>\<open>not\<close> clarify \<close>
    apply (thin_tac \<open>ss'(x := X) = ss\<close>)
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
    unfolding heap_alloc_rel_def precond_def
    apply (clarsimp simp add: nofailure_pred_sepconj_conj_distrib[symmetric] emp_def wlp_def
         sepconj_conj_def le_fun_def val_at_def plus_option_iff septract_conj_def imp_ex_conjL
         imp_conjL val_at_heap_def)
    apply (rename_tac ss ss' fl ls fs fls' fl')
    apply (subgoal_tac \<open>ls = Map.empty\<close>)
     prefer 2
     apply fast
    apply (elim disjE, blast)
    apply clarsimp
    apply (drule spec2, drule mp, assumption)
    apply (elim disjE, force)
    apply (metis map_empty_disjoint(2) option.distinct(1))
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
  defines \<open>precond \<equiv> \<lceil> \<lambda>ss. \<L> (pt \<^bold>\<mapsto> e ss) \<rceil>\<^sub>\<S> \<sqinter> \<S> p\<close>
    and \<open>postcond \<equiv> \<L> emp \<sqinter> \<S> p\<close>
  assumes
    \<open>(=) \<le> G\<close>
    \<open>wssa R precond \<le> I\<close>
    \<open>sswa R postcond \<le> I\<close>
    \<open>T RGSepAtom\<close>
    and frame_cond:
    \<open>F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> \<lceil> \<lambda>ss. \<L> (\<^bold>@\<^sub>\<H> pt ((#/#) (e ss))) \<rceil>\<^sub>\<S>\<close>
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

  have \<open>\<top> = (F \<sqinter> (wssa R precond \<midarrow>\<odot>\<^sub>\<and> \<top>) \<le> \<lceil> \<lambda>ss. \<L> (\<^bold>@\<^sub>\<H> pt ((#/#) (e ss))) \<rceil>\<^sub>\<S>)\<close>
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
     apply (subgoal_tac \<open>ls = [pt \<mapsto> e ss]\<close>)
      prefer 2
      apply (clarsimp simp add: precond_def wlp_def points_to_def; fail)
     apply (clarsimp simp add: precond_def postcond_def wlp_def emp_def disjoint_option_iff
        plus_option_iff val_at_heap_def)
     apply (metis fun_upd_triv fun_upd_upd not_dom_then_singleton_plus_heap_eq)
      (* \<Leftarrow> *)
    apply (rename_tac fs ss ls)
    apply (clarsimp simp add: val_at_heap_def)
    apply (drule_tac x=\<open>(=) (fs, ss)\<close> in spec, drule mp, fast)
    apply (subgoal_tac \<open>ls = [pt \<mapsto> e ss]\<close>)
     prefer 2
     apply (simp add: precond_def wlp_def points_to_def; fail)
    apply clarsimp
    apply (drule_tac x=\<open>[pt \<mapsto> e ss] + fs\<close> in spec, drule mp, force)
    apply (drule_tac x=\<open>[pt \<mapsto> e ss]\<close> in spec, drule mp)
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


section \<open> Misc \<close>

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

lemma maximal_heap_iff:
  \<open>(\<Sqinter>pt. \<Squnion>x. pt \<^bold>\<mapsto>\<^sup>\<Up> x) = (\<lambda>h. \<forall>pt. h pt \<noteq> None)\<close>
  by (simp add: fun_eq_iff points_to_dom_upcl_def)

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

lemma free_old_frame_cond_equiv:
  \<open>- \<L> (\<Squnion>v. pt \<^bold>\<mapsto>\<^sup>\<Up> v) = \<L> (\<^bold>@\<^sub>\<H> pt \<bottom>)\<close>
  by (clarsimp simp add: fun_eq_iff points_to_dom_upcl_def val_at_heap_def)

end