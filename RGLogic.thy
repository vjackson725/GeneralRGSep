theory RGLogic
  imports Lang
begin

section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

subsection \<open> rel relf + trans \<close>

lemma relyrel_trans: \<open>transp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
  by (metis rel_Times_left_eq_rtranclp_distrib transp_rtranclp)

lemma relyrel_mono: \<open>r1 \<le> r2 \<Longrightarrow> ((=) \<times>\<^sub>R r1\<^sup>*\<^sup>*) \<le> ((=) \<times>\<^sub>R r2\<^sup>*\<^sup>*)\<close>
  by (simp add: le_fun_def, metis mono_rtranclp)

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

lemmas sswa_rel_mono = sp_rel_mono[OF relyrel_mono]

lemmas wssa_weaker = wlp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma wssa_trivial[dest]:
  \<open>wssa r p x \<Longrightarrow> p x\<close>
  by (meson le_boolE le_funE wssa_weaker)

lemmas wssa_idem[simp] =
  wlp_comp_rel[where ?r1.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> and ?r2.0=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemmas wssa_rel_antimono = wlp_rel_antimono[OF relyrel_mono]


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
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L>(p) \<equiv> p \<circ> fst\<close>

abbreviation(input) shared_pred
  :: \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<S>\<close>)
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

lemma wssa_semiignore_local[simp]:
  \<open>\<L> pl \<^emph>\<and> wssa r q \<le> wssa r (\<L> pl \<^emph>\<and> q)\<close>
  \<open>wssa r p \<^emph>\<and> \<L> ql \<le> wssa r (p \<^emph>\<and> \<L> ql)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)+

text \<open>
  The full law local ignore law is _not_ true for \<open>wssa\<close>, unlike the one for \<open>sswa\<close>.
  Imagine the following situation:
    State model: \<open>bool \<times> bool\<close>
    Sep-algebra: \<open>R000, R011, R101, R111\<close>
    Inputs:
      \<open>q = {11, 00}\<close>
      \<open>r = (0 \<leadsto> 1, 0 \<leadsto> 1)\<close>
    Results:
      \<open>wssa r q = {}\<close>
      \<open>\<L> \<top> \<^emph>\<and> q = {11, 10, 00}\<close>
      \<open>(\<L> pl \<^emph>\<and> wssa r q) = {}\<close>
      \<open>wssa r (\<L> pl \<^emph>\<and> q) = {11, 10}\<close>
    Here we observe that the outputs are not the same, because \<open>wssa\<close> only preserves
    a \<^emph>\<open>subset\<close> of the initial predicate, and this subset might not be compatible
    with the frame.
\<close>

lemma sepconj_local_eq:
  \<open>\<L> p \<^emph>\<and> \<L> q = \<L> (p \<^emph> q)\<close>
  by (simp add: sepconj_conj_def sepconj_def fun_eq_iff)

lemma sepconj_shared_eq:
  \<open>(\<S> p :: 'a::multiunit_sep_alg \<times> 'b \<Rightarrow> bool) \<^emph>\<and> \<S> q = \<S> (p \<sqinter> q)\<close>
  by (force simp add: sepconj_conj_def sepconj_def fun_eq_iff)


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
  \<open>('l::perm_alg \<times> 's) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa r p \<le> q \<Longrightarrow> rgsat Skip r g p q F\<close>
| rgsat_iter:
  \<open>rgsat c r g (sswa r i) i F \<Longrightarrow>
    p \<le> wssa r i \<Longrightarrow>
    sswa r i \<le> q \<Longrightarrow>
    rgsat (Iter c) r g p q F\<close>
| rgsat_seq:
  \<open>rgsat c1 r g p1 p2 F \<Longrightarrow>
    rgsat c2 r g (p2) p3 F \<Longrightarrow>
    rgsat (c1 ;; c2) r g p1 p3 F\<close>
| rgsat_indet:
  \<open>rgsat c1 r g1 p q1 F \<Longrightarrow>
    rgsat c2 r g2 p q2 F \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<^bold>+ c2) r g p q F\<close>
| rgsat_endet:
  \<open>rgsat c1 r g1 p q1 F \<Longrightarrow>
    rgsat c2 r g2 p q2 F \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    q1 \<le> q \<Longrightarrow> q2 \<le> q \<Longrightarrow>
    rgsat (c1 \<box> c2) r g p q F\<close>
| rgsat_par:
  \<open>rgsat s1 (r \<squnion> g2) g1 p1 q1 \<top> \<Longrightarrow>
    rgsat s2 (r \<squnion> g1) g2 p2 q2 \<top> \<Longrightarrow>
    g1 \<le> g \<Longrightarrow> g2 \<le> g \<Longrightarrow>
    p \<le> p1 \<^emph>\<and> p2 \<Longrightarrow>
    sswa (r \<squnion> g2) (q1) \<^emph>\<and> sswa (r \<squnion> g1) (q2) \<le> q \<Longrightarrow>
    rgsat (s1 \<parallel> s2) r g p q \<top>\<close>
| rgsat_atom:
  \<open>p' \<le> wssa r p \<Longrightarrow>
    sswa r q \<le> q' \<Longrightarrow>
    p \<le> ap \<Longrightarrow>
    \<forall>f\<le>F. p \<^emph>\<and> \<L> f \<le> ap \<Longrightarrow>
    sp aq p \<le> q \<Longrightarrow>
    \<forall>f\<le>F. sp aq (p \<^emph>\<and> \<L> f) \<le> q \<^emph>\<and> \<L> f \<Longrightarrow>
    rel_liftL p \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    \<forall>f\<le>F. rel_liftL (p \<^emph>\<and> \<L> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g \<Longrightarrow>
    rgsat (Atomic ap aq) r g p' q' F\<close>
| rgsat_frame:
  \<open>rgsat c r g p q F \<Longrightarrow>
    p' \<le> p \<^emph>\<and> f \<Longrightarrow>
    q \<^emph>\<and> f' \<le> q' \<Longrightarrow>
    sswa (r \<squnion> g) f \<le> f' \<Longrightarrow>
    f' \<le> F \<times>\<^sub>P \<top> \<Longrightarrow>
    rgsat c r g p' q' (F \<midarrow>\<^emph> F)\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' F' \<Longrightarrow>
    p \<le> p' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    r \<le> r' \<Longrightarrow>
    g' \<le> g \<Longrightarrow>
    F \<le> F' \<Longrightarrow>
    rgsat c r g p q F\<close>
| rgsat_Disj:
  \<open>p' \<le> \<Squnion>P \<Longrightarrow>
    \<forall>p\<in>P. rgsat c r g p q F \<Longrightarrow>
    rgsat c r g p' q F\<close>
| rgsat_Conj:
  \<open>\<forall>q\<in>Q. rgsat c r g p q F \<Longrightarrow>
    Q \<noteq> {} \<Longrightarrow>
    \<forall>a b c. F c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    \<Sqinter>Q \<le> q' \<Longrightarrow>
    rgsat c r g p q' F\<close>

abbreviation rgsat_pretty
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close>
  (\<open>_, _ \<turnstile>\<^bsub>_\<^esub> { _ } _ { _ }\<close> [55, 55, 0, 55, 55, 55] 56) where
  \<open>r, g \<turnstile>\<^bsub>F\<^esub> { p } c { q } \<equiv> rgsat c r g p q F\<close>

inductive_cases rgsat_skipE[elim]: \<open>rgsat Skip r g p q F\<close>
inductive_cases rgsat_seqE[elim]: \<open>rgsat (c1 ;; c2) r g p q F\<close>
inductive_cases rgsat_iterE[elim]: \<open>rgsat (DO c OD) r g p q F\<close>
inductive_cases rgsat_parE[elim]: \<open>rgsat (c1 \<parallel> c2) r g p q F\<close>
inductive_cases rgsat_atomE[elim]: \<open>rgsat (Atomic ap aq) r g p q F\<close>
inductive_cases rgsat_indetE[elim]: \<open>rgsat (c1 \<^bold>+ c2) r g p q F\<close>
inductive_cases rgsat_endetE[elim]: \<open>rgsat (c1 \<box> c2) r g p q F\<close>

lemma backwards_done:
  \<open>rgsat Skip r g (wssa r p) p F\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wssa r p\<close> and q'=p])
    (clarsimp simp add: sp_def wlp_def le_fun_def split: sum.split)+

lemma rgsat_impossible[intro]:
  \<open>rgsat c r g \<bottom> q F\<close>
  using rgsat_Disj[of \<open>\<bottom>\<close> \<open>{}\<close>] by fastforce

lemma rgsat_disj:
  \<open>rgsat c r g p1 q F \<Longrightarrow>
    rgsat c r g p2 q F \<Longrightarrow>
    rgsat c r g (p1 \<squnion> p2) q F\<close>
  using rgsat_Disj[of \<open>p1 \<squnion> p2\<close> \<open>{p1,p2}\<close>]
  by fastforce

lemma rgsat_conj:
  \<open>rgsat c r g p q1 F \<Longrightarrow>
    rgsat c r g p q2 F \<Longrightarrow>
    \<forall>a b c. F c \<longrightarrow> a ## c \<longrightarrow> b ## c \<longrightarrow> a + c = b + c \<longrightarrow> a = b \<Longrightarrow>
    rgsat c r g p (q1 \<sqinter> q2) F\<close>
  using rgsat_Conj[of \<open>{q1,q2}\<close> _ _ _ _ _ \<open>q1 \<sqinter> q2\<close>]
  by fastforce

text \<open>
  The strongest weakening rule we can prove by induction. This is because parallel has the
  pessimistic frame set \<open>\<top>\<close>, which this rule inherits, and frame stabilisation requires the
  guarantee does not weaken is the same.
  It is nevertheless sound to use the stronger version.
\<close>
lemma rgsat_weak_weaken:
  \<open>rgsat c r' g p' q' \<top> \<Longrightarrow>
      p \<le> p' \<Longrightarrow>
      q' \<le> q \<Longrightarrow>
      r \<le> r' \<Longrightarrow>
      rgsat c r g p q \<top>\<close>
  apply (induct arbitrary: r p q rule: rgsat.inducts)
            apply (meson rgsat_skip order.trans relyrel_mono sp_mono; fail)
           apply (rule_tac i=i in rgsat_iter)
             apply (metis order.refl sswa_rel_mono)
            apply (meson order.trans relyrel_mono wlp_rel_antimono; fail)
           apply (meson order.trans relyrel_mono sp_rel_mono; fail)
          apply (meson order_refl rgsat_seq; fail)
         apply (meson rgsat_indet; fail)
        apply (meson rgsat_endet; fail)
      apply (rule_tac ?p1.0=p1 and ?p2.0=p2 and ?q1.0=q1 and ?q2.0=q2 and
      ?g1.0=g1 and ?g2.0=g2 in rgsat_par)
           apply (meson order.refl sup_mono; fail)
          apply (meson order.refl sup_mono; fail)
         apply order
        apply order
       apply order
      apply (meson order.trans le_disj_eq_absorb relyrel_mono sepconj_conj_mono sp_mono sup_mono; fail)
    (* atom *)
      apply (rule_tac p=p and q=q in rgsat_atom)
             apply (meson order.trans rel_Times_mono_right rtranclp_mono wlp_rel_antimono; fail)
            apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono; fail)
           apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono; fail)
          apply (intro allI impI, drule spec, drule mp, assumption)
          apply (meson order.trans rel_Times_mono_right rtranclp_mono sepconj_conj_monoL sp_pred_mono
      sp_rel_mono; fail)
         apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono wlp_rel_antimono
      inf_mono order_le_less sp_pred_mono; fail)
        apply (intro allI impI, drule spec, drule mp, assumption)
        apply (meson order.trans rel_Times_mono_right rtranclp_mono sp_rel_mono wlp_rel_antimono
      sepconj_conj_monoL sp_pred_mono; fail)
       apply (meson order.trans inf_mono le_disj_eq_absorb liftL_mono relyrel_mono sp_rel_mono; fail)
      apply blast
    (* frame *)
    apply (rule_tac p=p and q=q and r=ra in rgsat_frame)
        apply blast
       apply (rule order.trans; assumption)
      apply (rule order.trans; assumption)
     apply (meson order.refl order.trans sp_rel_mono relyrel_mono sup_mono; fail)
     apply blast
    (* weaken *)
    apply (meson rgsat_weaken; fail)
    (* Disj *)
   apply (rule_tac P=P in rgsat_Disj; simp; fail)
    (* Conj *)
  apply (rule_tac Q=Q in rgsat_Conj; simp; fail)
  done


end