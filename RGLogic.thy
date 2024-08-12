theory RGLogic
  imports Lang
begin

section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

subsection \<open> step properties \<close>

lemma sp_rely_step:
  \<open>r y y' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R rx) p (x, y) \<Longrightarrow>
    sp ((=) \<times>\<^sub>R (rx OO r)) p (x, y')\<close>
  by (force simp add: sp_def)

lemma sswa_step:
  \<open>r y y' \<Longrightarrow>
    sswa r p (x, y) \<Longrightarrow>
    sswa r p (x, y')\<close>
  by (simp add: sp_def, meson rtranclp.rtrancl_into_rtrancl)

lemmas sswa_stepD = sswa_step[rotated]

lemma wssa_step:
  \<open>r y y' \<Longrightarrow>
    wssa r p (x, y) \<Longrightarrow>
    wssa r p (x, y')\<close>
  by (simp add: wlp_def converse_rtranclp_into_rtranclp)

lemmas wssa_stepD = wssa_step[rotated]

subsection \<open> closure operator properties \<close>

lemmas sswa_stronger = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma sswa_trivial[intro]:
  \<open>p x \<Longrightarrow> sswa r p x\<close>
  by (simp add: sp_refl_relI)

lemmas sswa_idem[simp] =
  sp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

thm sp_mono

lemmas wssa_weaker = wlp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma wssa_trivial[dest]:
  \<open>wssa r p x \<Longrightarrow> p x\<close>
  by (meson le_boolE le_funE wssa_weaker)

lemmas wssa_idem[simp] =
  wlp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

thm wlp_mono


lemmas rely_rel_wlp_impl_sp =
  refl_rel_wlp_impl_sp[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]


subsection \<open> distributivity properties \<close>

lemma wlp_rely_sepconj_conj_semidistrib_mono:
  \<open>p' \<le> wlp ((=) \<times>\<^sub>R r) p \<Longrightarrow>
    q' \<le> wlp ((=) \<times>\<^sub>R r) q \<Longrightarrow>
    p' \<^emph>\<and> q' \<le> wlp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q)\<close>
  by (fastforce simp add: wlp_def sepconj_conj_def le_fun_def)

lemmas wlp_rely_sepconj_conj_semidistrib =
  wlp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma sp_rely_sepconj_conj_semidistrib_mono:
  \<open>sp ((=) \<times>\<^sub>R r) p \<le> p' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) q \<le> q' \<Longrightarrow>
    sp ((=) \<times>\<^sub>R r) (p \<^emph>\<and> q) \<le> p' \<^emph>\<and> q'\<close>
  by (fastforce simp add: sp_def sepconj_conj_def le_fun_def)

lemmas sp_rely_sepconj_conj_semidistrib =
  sp_rely_sepconj_conj_semidistrib_mono[OF order.refl order.refl]

lemma wssa_of_pred_Times_eq[simp]:
  \<open>wssa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P wlp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def wlp_def split: prod.splits)

lemma sp_rely_of_pred_Times_eq[simp]:
  \<open>sswa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P sp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_Times_def pred_Times_def sp_def split: prod.splits)

subsection \<open> Local and shared predicate lifting \<close>

abbreviation(input) local_pred
  :: \<open>('a::perm_alg \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L>(p) \<equiv> p \<circ> fst\<close>

abbreviation(input) shared_pred
  :: \<open>('b::perm_alg \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<S>\<close>)
  where
    \<open>\<S>(p) \<equiv> p \<circ> snd\<close>

lemma wssa_ignore_local[simp]:
  \<open>wssa r (\<L> pl) = \<L> pl\<close>
  by (fastforce simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_ignore_local[simp]:
  \<open>sswa r (\<L> pl) = \<L> pl\<close>
  \<open>sswa r (\<L> pl \<^emph>\<and> q) = \<L> pl \<^emph>\<and> sswa r q\<close>
  \<open>sswa r (p \<^emph>\<and> \<L> ql) = sswa r p \<^emph>\<and> \<L> ql\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)+

lemma wssa_over_shared:
  \<open>wssa r (\<S> ps) = \<S> (wlp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_over_shared:
  \<open>sswa r (\<S> ps) = \<S> (sp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)


section \<open> Framed step relation \<close>

context perm_alg
begin

text \<open>
  This predicate ensures that an update between two subresources preserve the rest of the heap.
  We need this in the perm_alg case, when we don't necessarily have a unit.
\<close>

definition
  \<open>framed_subresource_rel p ha ha' h h' \<equiv>
    (\<exists>hf. p hf \<and> ha ## hf \<and> ha' ## hf \<and> h = ha + hf \<and> h' = ha' + hf)\<close>

definition
  \<open>weak_framed_subresource_rel p ha ha' h h' \<equiv>
    ha = h \<and> ha' = h' \<or> framed_subresource_rel p ha ha' h h'\<close>

lemma framed_subresource_relI:
  \<open>p hf \<Longrightarrow> ha ## hf \<Longrightarrow> ha' ## hf \<Longrightarrow> h = ha + hf \<Longrightarrow> h' = ha' + hf \<Longrightarrow>
    framed_subresource_rel p ha ha' h h'\<close>
  by (force simp add: framed_subresource_rel_def)

lemma framed_subresource_rel_refl[intro!]:
  \<open>weak_framed_subresource_rel p h h' h h'\<close>
  by (simp add: weak_framed_subresource_rel_def)

lemma framed_subresource_rel_impl_weak[intro]:
  \<open>framed_subresource_rel p hx hx' h h' \<Longrightarrow> weak_framed_subresource_rel p hx hx' h h'\<close>
  using weak_framed_subresource_rel_def by force

lemma framed_subresource_rel_frame_second:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap_lr partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_frame:
  \<open>framed_subresource_rel \<top> ha ha' h h' \<Longrightarrow>
    h ## hf \<Longrightarrow>
    h' ## hf \<Longrightarrow>
    framed_subresource_rel \<top> ha ha' (h + hf) (h' + hf)\<close>
  using disjoint_add_swap_lr partial_add_assoc2
  by (simp add: framed_subresource_rel_def, meson)

lemma framed_subresource_rel_sym:
  \<open>framed_subresource_rel p a b a' b' \<Longrightarrow> framed_subresource_rel p b a b' a'\<close>
  using framed_subresource_rel_def by auto

lemma framed_subresource_le_firstD[dest]:
  \<open>framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha \<preceq> h\<close>
  using framed_subresource_rel_def partial_le_plus by force

lemma framed_subresource_le_secondD[dest]:
  \<open>framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha' \<preceq> h'\<close>
  using framed_subresource_rel_def partial_le_plus by auto

lemma wframed_subresource_le_firstD[dest]:
  \<open>weak_framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha \<preceq> h\<close>
  using weak_framed_subresource_rel_def by auto

lemma wframed_subresource_le_secondD[dest]:
  \<open>weak_framed_subresource_rel f ha ha' h h' \<Longrightarrow> ha' \<preceq> h'\<close>
  using weak_framed_subresource_rel_def by auto

lemma framed_subresource_rel_top_same_sub_iff[simp]:
  \<open>framed_subresource_rel f a a b b' \<longleftrightarrow> b = b' \<and> (\<exists>xf. a ## xf \<and> b = a + xf \<and> f xf)\<close>
  by (force simp add: framed_subresource_rel_def)

definition \<open>framecl r \<equiv> (\<lambda>a b. (\<exists>x y. r x y \<and> framed_subresource_rel \<top> x y a b))\<close>

lemma framecl_frame_closed:
  \<open>(x ## hf) \<Longrightarrow> (y ## hf) \<Longrightarrow> b x y \<Longrightarrow> framecl b (x + hf) (y + hf)\<close>
  by (force simp add: framecl_def framed_subresource_rel_def)

end

context multiunit_sep_alg
begin

lemma mu_sep_alg_compatible_framed_subresource_rel_iff:
  assumes
    \<open>compatible h h'\<close>
    \<open>p (unitof h)\<close>
  shows
  \<open>weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  using assms
  apply (simp add: weak_framed_subresource_rel_def framed_subresource_rel_def)
  apply (metis compatible_then_same_unit unitof_disjoint2 unitof_is_unitR2)
  done

end

lemma (in sep_alg) sep_alg_framed_subresource_rel_iff:
  \<open>p 0 \<Longrightarrow>
    weak_framed_subresource_rel p ha ha' h h' \<longleftrightarrow> framed_subresource_rel p ha ha' h h'\<close>
  by (force simp add: weak_framed_subresource_rel_def framed_subresource_rel_def)


section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat ::
  \<open>('l::perm_alg \<times> 's::perm_alg) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow> ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa r p \<le> q \<Longrightarrow> rgsat Skip r g p q\<close>
| rgsat_iter:
  \<open>rgsat c r g (sswa r i) (sswa r i) \<Longrightarrow>
    p \<le> i \<Longrightarrow> sswa r i \<le> q \<Longrightarrow>
    rgsat (Iter c) r g p q\<close>
| rgsat_seq:
  \<open>rgsat c1 r g p1 p2 \<Longrightarrow>
    rgsat c2 r g p2 p3 \<Longrightarrow>
    rgsat (c1 ;; c2) r g p1 p3\<close>
| rgsat_indet:
  \<open>rgsat c1 r g1 p q1 \<Longrightarrow>
    rgsat c2 r g2 p q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<^bold>+ c2) r g p q\<close>
| rgsat_endet:
  \<open>rgsat c1 r g1 p q1 \<Longrightarrow>
    rgsat c2 r g2 p q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<box> c2) r g p q\<close>
| rgsat_par:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<^emph>\<and> p2 \<Longrightarrow>
    sswa (r \<squnion> g2) q1 \<^emph>\<and> sswa (r \<squnion> g1) q2 \<le> q \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g p q\<close>
| rgsat_atom:
  \<open>p' \<le> wssa r p \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    sp b (wssa r p) \<le> sswa r q \<Longrightarrow>
    \<forall>f. sp b (wssa r (p \<^emph>\<and> \<L> f)) \<le> sswa r (q \<^emph>\<and> \<L> f) \<Longrightarrow>
    b \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    rgsat (Atomic b) r g p' q'\<close>
| rgsat_frame:
  \<open>rgsat c r g p q \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> f' \<Longrightarrow>
    rgsat c r g (p \<^emph>\<and> f) (q \<^emph>\<and> f')\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' \<Longrightarrow>
    p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> r \<le> r' \<Longrightarrow> g' \<le> g \<Longrightarrow>
    rgsat c r g p q\<close>
| rgsat_disj:
  \<open>rgsat c r g p1 q1 \<Longrightarrow>
    rgsat c r g p2 q2 \<Longrightarrow>
    rgsat c r g (p1 \<squnion> p2) (q1 \<squnion> q2)\<close>
| rgsat_conj:
  \<open>rgsat c r g p1 q1 \<Longrightarrow>
    rgsat c r g p2 q2 \<Longrightarrow>
    \<forall>a b c::'l. a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    rgsat c r g (p1 \<sqinter> p2) (q1 \<sqinter> q2)\<close>

abbreviation rgsat_pretty
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close>
  (\<open>_, _ \<turnstile> { _ } _ { _ }\<close> [55, 55, 55, 55, 55] 56) where
  \<open>r, g \<turnstile> { p } c { q } \<equiv> rgsat c r g p q\<close>

inductive_cases rgsep_doneE[elim]: \<open>rgsat Skip r g p q\<close>
inductive_cases rgsep_iterE[elim]: \<open>rgsat (DO c OD) r g p q\<close>
\<comment> \<open> inductive_cases rgsep_fixptE[elim]: \<open>rgsat (\<mu> c) r g p q\<close> \<close>
inductive_cases rgsep_parE[elim]: \<open>rgsat (s1 \<parallel> s2) r g p q\<close>
inductive_cases rgsep_atomE[elim]: \<open>rgsat (Atomic c) r g p q\<close>

lemma backwards_done:
  \<open>rgsat Skip r g (wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p) p\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*) p\<close> and q'=p])
    (clarsimp simp add: sp_def wlp_def le_fun_def)+

lemma rgsat_ex:
  \<open>rgsat c r g p q' \<Longrightarrow> q' = q x \<Longrightarrow> rgsat c r g p (\<lambda>y. \<exists>x. q x y)\<close>
  apply (induct arbitrary: q x rule: rgsat.inducts)
            apply (rule rgsat_skip)
            apply (force simp add: sp_def le_fun_def imp_ex_conjL)
           apply (rule rgsat_iter, force, force)
           apply (simp add: sp_def le_fun_def imp_ex_conjL; metis)
          apply (rule rgsat_seq; force)
         apply (rule rgsat_indet, fast, fast, fast, fast, fast, fast)
        apply (rule rgsat_endet, fast, fast, fast, fast, fast, fast)
       apply (rule rgsat_par; blast)
      apply (rule rgsat_atom; blast)
     apply (rule rgsat_weaken, (rule rgsat_frame; blast); force)
    apply (rule rgsat_weaken, blast, blast, blast, blast, blast)
   apply (rule rgsat_weaken, rule_tac ?p1.0=p1 and ?p2.0=p2 and ?q1.0=q1 and ?q2.0=q2 in rgsat_disj)
        apply blast
       apply blast
      apply (simp; fail)
     apply (clarsimp, blast)
    apply blast
   apply blast
  apply (rule rgsat_weaken, rule_tac ?p1.0=p1 and ?p2.0=p2 and ?q1.0=q1 and ?q2.0=q2 in rgsat_conj)
        apply blast
       apply blast
      apply (simp; fail)
     apply (simp; fail)
    apply (clarsimp, blast)
   apply blast
  apply blast
  done

end