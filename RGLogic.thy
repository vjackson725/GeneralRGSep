theory RGLogic
  imports SepAlgInstances Lang
begin

section \<open> RG Logic Utils \<close>

section \<open> rely/guarantee helpers \<close>

abbreviation \<open>sswa r \<equiv> sp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>
abbreviation \<open>wssa r \<equiv> wlp ((=) \<times>\<^sub>R r\<^sup>*\<^sup>*)\<close>

lemmas relyrel_trans = rel_times_trans[OF transp_equality transp_rtranclp]
lemmas relyrel_mono = rel_times_mono[OF order.refl rtranclp_mono]


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

lemmas wssa_stronger_strengthen =
  transp_wlp_stronger_strengthen[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified,
    OF _ relyrel_trans]

lemmas rely_rel_wlp_impl_sp =
  refl_rel_wlp_impl_sp[of \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> \<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma sswa_bot_rel_eq[simp]:
  \<open>sswa \<bottom> p = p\<close>
  by (clarsimp simp add: sp_def fun_eq_iff)
    (metis (full_types) rtranclp_eq_eq rtranclp_reflclp sup_bot_left)

lemma wssa_bot_rel_eq[simp]:
  \<open>wssa \<bottom> p = p\<close>
  by (clarsimp simp add: wlp_def fun_eq_iff)
    (metis (full_types) rtranclp_eq_eq rtranclp_reflclp sup_bot_left)


subsection \<open> absorption/pseduo-idempotence properties \<close>

lemma sswa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(1) sp_relcomp)

lemma wssa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (wssa r2 p) = wssa r2 p\<close>
  by (simp add: rel_le_rtranscp_relcompp_absorb(2) wlp_relcomp)

lemma sswa_over_wssa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> sswa r1 (wssa r2 p) = wssa r2 p\<close>
  by (force simp add: relyrel_trans relyrel_mono sp_wlp_absorb)

lemma wssa_over_sswa_eq[simp]:
  \<open>r1 \<le> r2 \<Longrightarrow> wssa r1 (sswa r2 p) = sswa r2 p\<close>
  by (simp add: relyrel_mono relyrel_trans wlp_sp_absorb)


subsection \<open> sswa closure / wssa interior \<close>

paragraph \<open> sswa closure \<close>

lemmas sswa_weaker = sp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma sswa_trivial[intro]:
  \<open>p x \<Longrightarrow> sswa r p x\<close>
  by (simp add: sp_refl_relI)

\<comment> \<open> sswa_idem \<close>
thm sswa_over_sswa_eq[OF order.refl]

lemmas sswa_rel_mono = sp_rel_mono[OF relyrel_mono]


paragraph \<open> wssa interior \<close>

lemmas wssa_stronger = wlp_refl_rel_le[where r=\<open>(=) \<times>\<^sub>R r\<^sup>*\<^sup>*\<close> for r, simplified]

lemma wssa_trivial[dest]:
  \<open>wssa r p x \<Longrightarrow> p x\<close>
  by (drule wlp_refl_relD[rotated], simp)

\<comment> \<open> wssa_idem \<close>
thm wssa_over_wssa_eq[OF order.refl]

lemmas wssa_rel_antimono = wlp_rel_antimono[OF relyrel_mono]


subsection \<open> semi-distributivity with sepconj-conj \<close>

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

lemma sswa_eqpred_eq:
  \<open>sswa R ((=) s) = ((=) (fst s)) \<times>\<^sub>P (sp R\<^sup>*\<^sup>* ((=) (snd s)))\<close>
  by (force simp add: fun_eq_iff sp_def)

lemma wssa_eqpred_eq:
  \<open>wssa R ((=) s) = ((=) (fst s)) \<times>\<^sub>P (wlp R\<^sup>*\<^sup>* ((=) (snd s)))\<close>
  by (force simp add: fun_eq_iff wlp_def)


subsection \<open> Interaction with pred-Times \<close>

lemma wssa_of_pred_Times_eq[simp]:
  \<open>wssa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P wlp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_times_def pred_times_def wlp_def split: prod.splits)

lemma sp_rely_of_pred_Times_eq[simp]:
  \<open>sswa r (p \<times>\<^sub>P q) = (p \<times>\<^sub>P sp r\<^sup>*\<^sup>* q)\<close>
  by (force simp add: rel_times_def pred_times_def sp_def split: prod.splits)


subsection \<open> Local and shared predicate lifting \<close>

abbreviation(input) local_pred
  :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<L>\<close>)
  where
    \<open>\<L>(p) \<equiv> p \<circ> fst\<close>

abbreviation(input) shared_pred
  :: \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)\<close> (\<open>\<S>\<close>)
  where
    \<open>\<S>(p) \<equiv> p \<circ> snd\<close>

lemma sepconj_local_eq:
  \<open>\<L> p \<^emph>\<and> \<L> q = \<L> (p \<^emph> q)\<close>
  by (simp add: sepconj_conj_def sepconj_def fun_eq_iff)

lemma sepconj_shared_eq:
  \<open>(\<S> p :: 'a::multiunit_sep_alg \<times> 'b \<Rightarrow> bool) \<^emph>\<and> \<S> q = \<S> (p \<sqinter> q)\<close>
  by (force simp add: sepconj_conj_def sepconj_def fun_eq_iff)


subsection \<open> wssa/sswa on local/shared pred \<close>

lemma wssa_ignore_local[simp]:
  \<open>wssa r (\<L> pl) = \<L> pl\<close>
  by (fastforce simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_ignore_local[simp]:
  \<open>sswa r (\<L> pl) = \<L> pl\<close>
  \<open>sswa r (\<L> pl \<^emph>\<and> q) = \<L> pl \<^emph>\<and> sswa r q\<close>
  \<open>sswa r (p \<^emph>\<and> \<L> ql) = sswa r p \<^emph>\<and> \<L> ql\<close>
  \<open>sswa r (\<L> pl \<sqinter> q) = \<L> pl \<sqinter> sswa r q\<close>
  \<open>sswa r (p \<sqinter> \<L> ql) = sswa r p \<sqinter> \<L> ql\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)+

lemma wssa_over_shared:
  \<open>wssa r (\<S> ps) = \<S> (wlp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: wlp_def fun_eq_iff sepconj_conj_def)

lemma sswa_over_shared:
  \<open>sswa r (\<S> ps) = \<S> (sp r\<^sup>*\<^sup>* ps)\<close>
  by (force simp add: sp_def fun_eq_iff sepconj_conj_def)

lemma wssa_ignore_local_when_shared:
  \<open>wssa r (\<L> p \<^emph>\<and> \<S> q) = \<L> p \<^emph>\<and> wssa r (\<S> q)\<close>
  \<open>wssa r (\<S> q \<^emph>\<and> \<L> p) = wssa r (\<S> q) \<^emph>\<and> \<L> p\<close>
  by (clarsimp simp add: wlp_def fun_eq_iff sepconj_conj_def, metis rtranclp.rtrancl_refl)+

lemma wssa_semiignore_local:
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

lemma shared_sepconj_conj_eq:
  \<open>(\<S> p \<^emph>\<and> q) = \<S> p \<sqinter> (\<top> \<^emph>\<and> q)\<close>
  \<open>(q \<^emph>\<and> \<S> p) = \<S> p \<sqinter> (q \<^emph>\<and> \<top>)\<close>
  by (force simp add: sepconj_conj_def fun_eq_iff)+


section \<open> Definitions for the Program Logic \<close>

definition
  \<open>cancellative' Ia Ib F \<equiv>
    \<forall>lsa lsb fs ss.
      Ia (lsa, ss) \<longrightarrow> Ib (lsb, ss) \<longrightarrow>
      F (fs, ss) \<longrightarrow>
      lsa ## fs \<longrightarrow> lsb ## fs \<longrightarrow>
      lsa + fs = lsb + fs \<longrightarrow> lsa = lsb\<close>

definition \<open>any_shared p \<equiv> pred_image fst p \<times>\<^sub>P \<top>\<close>

lemma any_shared_apply[simp]:
  \<open>any_shared p (ls, ss) = (\<exists>ss. p (ls, ss))\<close>
  by (simp add: any_shared_def)

lemma self_implies_self_any_shared:
  \<open>p \<le> any_shared p\<close>
  by force

lemma any_shared_idem[simp]:
  \<open>any_shared (any_shared p) = any_shared p\<close>
  by force


section \<open> Rely-Guarantee Separation Logic \<close>

\<comment> \<open> We are going to need to be able to introspect on the rule form. \<close>
datatype rgsep_rule =
  RGSepSkip |
  RGSepIter |
  RGSepSeq |
  RGSepIndet |
  RGSepEndet |
  RGSepPar |
  RGSepAtom |
  RGSepFrame |
  RGSepWeaken |
  RGSepDisj |
  RGSepConj

lemma
  \<open>(\<forall>f\<le>F. sp ar (wssa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> sp ((=) \<times>\<^sub>R G) f) \<Longrightarrow>
    rel_image snd (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> ar) \<le> G\<close>
  apply (clarsimp simp add: le_fun_def sp_def sepconj_conj_def wlp_def)
  apply (drule spec, drule mp, force)
  apply (rename_tac ss ss' ls lfs' fs)
  apply (clarsimp simp add: imp_ex_conjL)
  apply (drule spec2, drule spec2, drule mp, force)
  apply (drule spec2, drule mp, fast, drule mp, fast)
  apply clarsimp
  oops

(* TODO: reverse F I *)
inductive rgsat ::
  \<open>('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    (rgsep_rule \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa R p \<le> q \<Longrightarrow>
    sswa R p \<le> I \<Longrightarrow>
    T RGSepSkip \<Longrightarrow>
    rgsat Skip R G p q I F T\<close>
| rgsat_iter:
  \<open>rgsat c R G (sswa R i) i I F T \<Longrightarrow>
    sswa R p \<le> i \<Longrightarrow>
    sswa R i \<le> q \<Longrightarrow>
    T RGSepIter \<Longrightarrow>
    rgsat (Iter c) R G p q I F T\<close>
| rgsat_seq:
  \<open>rgsat ca R G p pp Ia F T \<Longrightarrow>
    rgsat cb R G pp q Ib F T \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    T RGSepSeq \<Longrightarrow>
    rgsat (ca ;; cb) R G p q I F T\<close>
| rgsat_indet:
  \<open>rgsat ca R Ga p qa Ia F T \<Longrightarrow>
    rgsat cb R Gb p qb Ib F T \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    T RGSepIndet \<Longrightarrow>
    rgsat (ca \<^bold>\<sqinter> cb) R G p q I F T\<close>
| rgsat_endet:
  \<open>rgsat ca R Ga p qa Ia F T \<Longrightarrow>
    rgsat cb R Gb p qb Ib F T \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    T RGSepEndet \<Longrightarrow>
    rgsat (ca \<^bold>\<box> cb) R G p q I F T\<close>
| rgsat_par:
  \<open>rgsat ca (R \<squnion> Gb) Ga pa qa Ia (Ib \<^emph>\<and> F) T \<Longrightarrow>
    rgsat cb (R \<squnion> Ga) Gb pb qb Ib (Ia \<^emph>\<and> F) T \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    p \<le> pa \<^emph>\<and> pb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    T RGSepPar \<Longrightarrow>
    rgsat (ca \<parallel> cb) R G p q I F T\<close>
| rgsat_atom:
  \<open>p' \<le> wssa R p \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    \<comment> \<open> step \<close>
    \<forall>f\<le>F. sp ar (wssa R p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f \<Longrightarrow>
    \<comment> \<open> guarantee condition \<close>
    rel_image snd (rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> ar) \<le> G \<Longrightarrow>
    \<comment> \<open> misc \<close>
    wssa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    T RGSepAtom \<Longrightarrow>
    rgsat \<langle>ar\<rangle> R G p' q' I F T\<close>
| rgsat_frame:
  \<open>rgsat c R G p q I (F \<^emph>\<and> F') T \<Longrightarrow>
    sswa (R \<squnion> G) F' \<le> F' \<Longrightarrow>
    T RGSepFrame \<Longrightarrow>
    rgsat c R G (p \<^emph>\<and> F') (q \<^emph>\<and> F') (I \<^emph>\<and> F') F T\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' I' F' T \<Longrightarrow>
    p \<le> p' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    r \<le> r' \<Longrightarrow>
    g' \<le> g \<Longrightarrow>
    I' \<le> I \<Longrightarrow>
    F \<le> F' \<Longrightarrow>
    T RGSepWeaken \<Longrightarrow>
    rgsat c r g p q I F T\<close>
| rgsat_Disj:
  \<open>p' \<le> \<Squnion>P \<Longrightarrow>
    \<forall>p\<in>P. rgsat c R G p q I F T \<Longrightarrow>
    T RGSepDisj \<Longrightarrow>
    rgsat c R G p' q I F T\<close>
| rgsat_Conj:
  \<open>\<Sqinter>\<I> \<le> I' \<Longrightarrow>
    \<Sqinter>\<G> \<le> G' \<Longrightarrow>
    \<Sqinter>Q \<le> q' \<Longrightarrow>
    \<I> \<noteq> {} \<Longrightarrow>
    \<G> \<noteq> {} \<Longrightarrow>
    Q \<noteq> {} \<Longrightarrow>
    \<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. rgsat c R G p q I F T \<Longrightarrow>
    cancellative' (\<Squnion>\<I>) (\<Squnion>\<I>) (sswa (\<Squnion>\<G>) F) \<Longrightarrow>
    T RGSepConj \<Longrightarrow>
    rgsat c R G' p q' I' F T\<close>

abbreviation rgsat_pretty
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_, _, _, _, _ \<turnstile> { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>r, g, L, F, T \<turnstile> { p } c { q } \<equiv> rgsat c r g p q L F T\<close>

inductive_cases rgsat_skipE[elim]: \<open>rgsat Skip R G p q I F T\<close>
inductive_cases rgsat_seqE[elim]: \<open>rgsat (c1 ;; c2) R G p q I F T\<close>
inductive_cases rgsat_iterE[elim]: \<open>rgsat (DO c OD) R G p q I F T\<close>
inductive_cases rgsat_parE[elim]: \<open>rgsat (c1 \<parallel> c2) R G p q I F T\<close>
inductive_cases rgsat_atomE[elim]: \<open>rgsat \<langle>ar\<rangle> R G p q I F T\<close>
inductive_cases rgsat_indetE[elim]: \<open>rgsat (c1 \<^bold>\<sqinter> c2) R G p q I F T\<close>
inductive_cases rgsat_endetE[elim]: \<open>rgsat (c1 \<^bold>\<box> c2) R G p q I F T\<close>


lemmas rgsat_weaken_prepost = rgsat_weaken[OF _ _ _ order.refl order.refl order.refl order.refl]

lemma rgsat_stabilise_prepost:
  \<open>R, G, I, F, T \<turnstile> { sswa R p } c { wssa R q } \<Longrightarrow>
    T RGSepWeaken \<Longrightarrow>
    R, G, I, F, T \<turnstile> { p } c { q }\<close>
  using rgsat_weaken_prepost by blast

lemma rgsat_skip_forwards:
  \<open>T RGSepSkip \<Longrightarrow> rgsat Skip r g p (sswa r p) (sswa r p) F T\<close>
  by (rule rgsat_skip) force+

lemma rgsat_skip_backwards:
  \<open>T RGSepSkip \<Longrightarrow> T RGSepWeaken \<Longrightarrow> rgsat Skip r g (wssa r q) q q F T\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wssa r q\<close> and q'=q and I'=q and F'=F]) force+

lemma rgsat_impossible[intro]:
  \<open>T RGSepDisj \<Longrightarrow> rgsat c R G \<bottom> q I F T\<close>
  using rgsat_Disj[where P=\<open>{}\<close>]
  by blast

lemma rgsat_disj:
  \<open>rgsat c R G pa q I F T \<Longrightarrow>
    rgsat c R G pb q I F T \<Longrightarrow>
    T RGSepDisj \<Longrightarrow>
    rgsat c R G (pa \<squnion> pb) q I F T\<close>
  using rgsat_Disj[where P=\<open>{pa, pb}\<close>, OF order.refl]
  by simp

lemma rgsat_conj:
  \<open>rgsat c R G p qa I F T \<Longrightarrow>
    rgsat c R G p qb I F T \<Longrightarrow>
    cancellative' I I (sswa G F) \<Longrightarrow>
    T RGSepConj \<Longrightarrow>
    rgsat c R G p (qa \<sqinter> qb) I F T\<close>
  using rgsat_Conj[of \<open>{I}\<close> I \<open>{G}\<close> G \<open>{qa, qb}\<close> \<open>qa \<sqinter> qb\<close> c R p F T]
  by (simp add: rgsat_weaken[where I=\<top>] rgsat_weaken[where g=\<top>] rgsat_weaken[where q=\<top>])

lemma rgsat_precond_implies_stateinv:
  assumes \<open>R, G, I, F, T \<turnstile> { p } c { q }\<close>
  shows \<open>sswa R p \<le> I\<close>
  using assms
proof (induct rule: rgsat.inducts)
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F T cb pb qb G p q I)
  then show ?case
    apply -
    apply (rule order.trans[OF sp_pred_mono], assumption)
    apply (rule order.trans[OF sp_rely_sepconj_conj_semidistrib])
    apply (rule order.trans[rotated], assumption)
    apply (rule sepconj_conj_mono;
        meson order.trans sswa_rel_mono sswa_weaker sup_ge1)
    done
next
  case (rgsat_frame c R G p q I F F' C)
  then show ?case
    by (metis (mono_tags, lifting) order.trans sp_rely_sepconj_conj_semidistrib sepconj_conj_mono
        sswa_rel_mono sup_ge1)
next
  case (rgsat_weaken c R' G' p' q' I' F' T p q R G I F)
  then show ?case
    by (meson order.trans sp_pred_mono sswa_rel_mono)
next
  case (rgsat_Disj p' P c R G q I F C)
  then show ?case
    by (metis (no_types, lifting) Sup_le_iff converse_rtranclp_into_rtranclp rtranclp_less_eq
        wlp_weaker_iff_sp_stronger)
next
  case (rgsat_Conj \<I> I' \<G> G' Q q' c R p F C)
  then show ?case
    apply (clarsimp simp add: ball_conj_distrib imp_conjL ex_disj_distrib)
    apply (meson Inf1_I equals0I le_boolD le_funE)
    done
next
  case (rgsat_atom p' R p q q' ar G F I C)
  then show ?case
    by (meson order.trans wlp_weaker_iff_sp_stronger wssa_stronger_strengthen)
qed fast+

lemma rgsat_par_alt:
  \<open>rgsat ca (R \<squnion> Gb) Ga pa qa Ia (Ib \<^emph>\<and> F) T \<Longrightarrow>
    rgsat cb (R \<squnion> Ga) Gb pb qb Ib (Ia \<^emph>\<and> F) T \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    p \<le> pa \<^emph>\<and> pb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    T RGSepPar \<Longrightarrow>
    rgsat (ca \<parallel> cb) R G p q I F T\<close>
  apply (rule rgsat_par)
         apply blast
        apply blast
       apply blast
      apply blast
     apply blast
    apply blast
   apply (meson order_trans sepconj_conj_mono sswa_weaker; fail)
  apply blast
  done

text \<open>
  Not true. Both \<open>q\<close> and \<open>I\<close> establish bounds on what the state can be, but they don't prescribe
  what the state must be. Hence \<open>q\<close> and \<open>I\<close> can be completely unrelated. (In which case the program,
  upon termination, will actually be in a state that passes \<open>q \<sqinter> I\<close>.)
\<close>
lemma rgsat_postcond_implies_stateinv:
  assumes \<open>R, G, I, F, T \<turnstile> { p } c { q }\<close>
  shows \<open>q \<le> I\<close>
  nitpick[card 'a=1, card 'b=1]
  oops

text \<open>
  Not true, because the invariant can be weakened to something unstable.
\<close>
lemma rgsat_restrict_stateinv:
  assumes \<open>R, G, I, F, T \<turnstile> { p } c { q }\<close>
  shows \<open>R, G, wssa R I, F, T \<turnstile> { p } c { q }\<close>
  using assms
  oops



section \<open> Specialised Rules \<close>

subsection \<open> Await \<close>

lemma rgsat_await:
  assumes framed_step: \<open>\<forall>f\<le>F. (wssa R p \<^emph>\<and> f) \<sqinter> p' \<le> q \<^emph>\<and> any_shared f\<close>
    and guar: \<open>rel_image snd (rel_liftL ((wssa R p \<^emph>\<and> F) \<sqinter> p') \<sqinter> (=)) \<le> G\<close>
    and stinv:
    \<open>wssa R p \<le> I\<close>
    \<open>sswa R q \<le> I\<close>
    and cpred: \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { wssa R p } Await p' { sswa R q }\<close>
  using assms
  unfolding await_rel_def
  by (intro rgsat_atom[where p=p and q=q])
      (simp add: rel_liftL_conj_distrib inf.assoc)+

text \<open> Specialise the rule to the strongest \<open>q\<close> \<close>
lemma rgsat_await':
  assumes framed_step:
    \<open>\<forall>f\<le>F. (wssa R p \<^emph>\<and> f) \<sqinter> p' \<le> (wssa R p \<sqinter> p') \<^emph>\<and> any_shared f\<close>
    and guar: \<open>rel_image snd (rel_liftL ((wssa R p \<^emph>\<and> F) \<sqinter> p') \<sqinter> (=)) \<le> G\<close>
    and stinv:
    \<open>wssa R p \<le> I\<close>
    \<open>sswa R (wssa R p \<sqinter> p') \<le> I\<close>
    and cpred: \<open>T RGSepAtom\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { wssa R p } Await p' { sswa R (wssa R p \<sqinter> p') }\<close>
  using assms
  by (intro rgsat_await) blast+


text \<open>
  Note: the rule does not attempt to prevent the Await from deadlocking for no reason.
  One should also show that the Await-predicate is achievable from the current state
  with \<open>R\<close> steps. I.e. \<open>\<exists>s. sp R\<^sup>*\<^sup>* ((sswa R p \<^emph>\<and> F) \<sqinter> p') s\<close>
    This doesn't prevent all deadlocks, but does ensure that, if one does occur,
  some of the blame for it falls on the environment specification.
\<close>

\<comment> \<open> Technically a more general property about stable predicates and conjunction,
  but helpful for await in particular. \<close>
lemma await_post_stable_guard:
  \<open>sswa R p' \<le> p' \<Longrightarrow> sswa R (sswa R p \<sqinter> p') = sswa R p \<sqinter> p'\<close>
  by (metis order.eq_iff sp_inf_semidistrib sswa_over_sswa_eq sswa_weaker)


subsection \<open> If-then-else \<close>

lemma rgsat_if_then_else:
  assumes tt_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> (sswa R p \<sqinter> pp) \<^emph>\<and> any_shared f\<close>
    and ff_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> -pp \<le> (sswa R p \<sqinter> -pp) \<^emph>\<and> any_shared f\<close> 
    and body_assms:
    \<open>R, G, Ia, F, T \<turnstile> { sswa R (sswa R p \<sqinter> pp) } ctt { qa }\<close>
    \<open>R, G, Ib, F, T \<turnstile> { sswa R (sswa R p \<sqinter> -pp) } cff { qb }\<close>
    and misc_assms:
    \<open>rel_liftL (sswa R p \<^emph>\<and> F) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>Ia \<le> I\<close>
    \<open>Ib \<le> I\<close>
    \<open>qa \<le> wssa R q\<close>
    \<open>qb \<le> wssa R q\<close>
    \<open>T RGSepAtom\<close>
    \<open>T RGSepEndet\<close>
    \<open>T RGSepSeq\<close>
    \<open>T RGSepWeaken\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { p } IfThenElse pp ctt cff { q }\<close>
  using misc_assms
  unfolding IfThenElse_def
proof (intro
    rgsat_stabilise_prepost[OF
      rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
        where I=I and Ia=\<open>sswa R p \<squnion> Ia\<close> and Ib=\<open>sswa R p \<squnion> Ib\<close>]])
  show \<open>R, G, sswa R p, F, T \<turnstile> { sswa R p } Await pp { sswa R (sswa R p \<sqinter> pp) }\<close>
    using misc_assms assms(1) tt_guard_frame_cond
    apply (intro rgsat_await'[where R=R and p=\<open>sswa R p\<close>, simplified])
        apply blast
       apply (simp add: inf_sup_aci(2,3) le_infI2 rel_image_snd_galois rel_liftL_conj_eq; fail)
      apply blast
     apply (metis order.refl inf_sup_ord(1) wlp_weaker_iff_sp_stronger wssa_over_sswa_eq)
    apply blast
    done
  show \<open>R, G, Ia, F, T \<turnstile> { sswa R (sswa R p \<sqinter> pp) } ctt { qa }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, T \<turnstile> { sswa R p } Await (- pp) { sswa R (sswa R p \<sqinter> -pp) }\<close>
    using ff_guard_frame_cond misc_assms assms
    apply (intro rgsat_await'[where R=R and p=\<open>sswa R p\<close>, simplified])
        apply blast
       apply (simp add: inf_sup_aci(2,3) le_infI2 rel_image_snd_galois rel_liftL_conj_eq; fail)
      apply blast
     apply (metis order.refl inf_sup_ord(1) wlp_weaker_iff_sp_stronger wssa_over_sswa_eq)
    apply blast
    done
  show \<open>R, G, Ib, F, T \<turnstile> { sswa R (sswa R p \<sqinter> -pp) } cff { qb }\<close>
    using body_assms
    by blast
  show \<open>sswa R p \<squnion> Ia \<le> I\<close>
    using misc_assms
    by simp
  show \<open>sswa R p \<squnion> Ib \<le> I\<close>
    using misc_assms
    by simp
qed simp+

\<comment> \<open> Unfortunately, \<open>b\<close> and \<open>-b\<close> have to be separately shown to be stable. \<close>
lemma await_post_stable_neg_guard:
  \<open>sswa R p' \<le> p' \<Longrightarrow> sswa R (sswa R p \<sqinter> -p') = sswa R p \<sqinter> -p'\<close>
  nitpick[card 'a=1, card 'b=2]
  oops


subsection \<open> WhileLoop \<close>

lemma rgsat_while:
  assumes
    \<open>rel_image snd (rel_liftL ((sswa R ii \<^emph>\<and> F) \<sqinter> px) \<sqinter> (=)) \<le> G\<close>
    \<open>\<forall>f\<le>F. (sswa R ii \<^emph>\<and> f) \<sqinter> px \<le> (sswa R ii \<sqinter> px) \<^emph>\<and> any_shared f\<close>
    \<open>sswa R (sswa R ii \<sqinter> px) \<le> sswa R ii\<close>
    \<open>sswa R ii \<le> I\<close>
    \<open>sswa R p \<le> ii\<close>
    \<open>sswa R ii \<le> q\<close>
    and rgsat_body:
    \<open>R, G, I, F, T \<turnstile> { sswa R (sswa R ii \<sqinter> px) } c { ii }\<close>
    and misc_assms:
    \<open>T RGSepAtom\<close>
    \<open>T RGSepSeq\<close>
    \<open>T RGSepIter\<close>
  shows
    \<open>R, G, I, F, T \<turnstile> { p } WhileLoop px c { q }\<close>
  unfolding WhileLoop_def
  using assms
  by (intro rgsat_iter[where i=ii and I=I,
        OF rgsat_seq[where I=I and Ia=I and Ib=I and pp=\<open>sswa R (sswa R ii \<sqinter> px)\<close>,
          OF rgsat_atom[where p=\<open>sswa R ii\<close> and q=\<open>sswa R ii \<sqinter> px\<close>]]])
    (simp add: await_rel_def inf_assoc rel_liftL_conj_distrib; fail)+


section \<open> Atom Variants \<close>

text \<open>
  For the atom rule, show we don't need to conj with the atom-precondition
  in the sp assumption.
\<close>
lemma atom_pre_conj_unecessary:
  \<open>sswa R p \<^emph>\<and> F \<le> pa \<Longrightarrow> f \<le> F \<Longrightarrow> sswa R p \<^emph>\<and> f \<le> pa\<close>
  by (meson order.trans sepconj_conj_monoR)

text \<open>
  For atom, when we use the frame, one might question whether we wish to select \<^emph>\<open>all\<close> subpredicates
  of the frame predicate, or merely each frame in the frame predicate individually. Perhaps
  surprisingly, these two variants turn out to be the same.
\<close>

lemma atom_variant_pointwise_frame:
    \<open>(\<forall>f\<le>F. p \<^emph>\<and> f \<le> ap) \<longleftrightarrow> (\<forall>f. F f \<longrightarrow> p \<^emph>\<and> (=) f \<le> ap)\<close>
    \<open>(\<forall>f\<le>F. sp aq (p \<^emph>\<and> f) \<le> q \<^emph>\<and> f) \<longleftrightarrow> (\<forall>f. F f \<longrightarrow> sp aq (p \<^emph>\<and> (=) f) \<le> q \<^emph>\<and> (=) f)\<close>
    \<open>(\<forall>f\<le>F. rel_liftL (p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g) \<longleftrightarrow>
      (\<forall>f. F f \<longrightarrow> rel_liftL (p \<^emph>\<and> (=) f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g)\<close>
    apply (clarsimp simp add: le_fun_def sepconj_conj_def, metis)
   apply (rule order.antisym)
    apply (clarsimp simp add: le_fun_def; fail)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def sp_def imp_ex_conjL imp_conjL, blast)
  apply (clarsimp simp add: le_fun_def sepconj_conj_def, fast)
  done

text \<open>
  However, framing only by the frame predicate is not equivalent for every case,
  though it is equivalent in two.
\<close>
lemma atom_variant_compressed_frame:
    \<open>(\<forall>f\<le>F. p \<^emph>\<and> f \<le> ap) \<longleftrightarrow> p \<^emph>\<and> F \<le> ap\<close>
    \<open>(\<forall>f\<le>F. sp aq (p \<^emph>\<and> f) \<le> q \<^emph>\<and> f) \<longrightarrow> (sp aq (p \<^emph>\<and> F) \<le> q \<^emph>\<and> F)\<close>
    \<open>(\<forall>f\<le>F. rel_liftL (p \<^emph>\<and> f) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g) \<longleftrightarrow> rel_liftL (p \<^emph>\<and> F) \<sqinter> aq \<le> \<top> \<times>\<^sub>R g\<close>
    apply (clarsimp simp add: le_fun_def sepconj_conj_def; fast)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def sp_def imp_conjL imp_ex_conjL; fail)
  apply (rule order.antisym; simp add: le_fun_def sepconj_conj_def imp_conjL imp_ex_conjL; metis)
  done

lemma atom_variant_compressed_frame2_nequiv:
  fixes p q F :: \<open>'l::pre_perm_alg \<times> 's \<Rightarrow> bool\<close>
  shows
    \<open>sp aq (wssa r p \<^emph>\<and> F) \<le> q \<^emph>\<and> any_shared F \<longrightarrow>
      (\<forall>f\<le>F. sp aq (wssa r p \<^emph>\<and> f) \<le> q \<^emph>\<and> any_shared f)\<close>
  nitpick[card 'l=2, card 's=1]
  oops

lemma Sup_sepconjConj_framest_equiv_sepconjConj_frame:
  \<open>\<Squnion>{wssa R p \<^emph>\<and> f|f. f \<le> F} = (wssa R p \<^emph>\<and> F)\<close>
  apply (simp add: fun_eq_iff sepconj_conj_def)
  apply (intro iffI allI)
   apply (meson predicate1D; fail)
  apply clarsimp
  apply (rename_tac ss sl sf)
  apply (rule_tac
      x=\<open>\<lambda>(slf', ss'). (\<exists>sl. wssa R p (sl, ss') \<and> sl ## sf \<and> slf' = sl + sf) \<and> ss' = ss\<close> in
      exI)
  apply clarsimp
  apply (rule conjI[rotated], blast)
  apply (rule_tac x=\<open>(=) (sf, ss)\<close> in exI)
  apply blast
  done

lemma guar_rel_collapse_frames:
  \<open>\<Squnion>{rel_liftL (wssa R p \<^emph>\<and> f) \<sqinter> aq|f. f \<le> F} = rel_liftL (wssa R p \<^emph>\<and> F) \<sqinter> aq\<close>
proof -
  have \<open>\<Squnion>{rel_liftL (wssa R p \<^emph>\<and> f) \<sqinter> aq|f. f \<le> F} =
    \<Squnion>((\<lambda>x. rel_liftL x \<sqinter> aq) ` {wssa R p \<^emph>\<and> f|f. f \<le> F})\<close>
    by (clarsimp simp add: image_def, blast)
  also have \<open>... = rel_liftL (\<Squnion>{wssa R p \<^emph>\<and> f|f. f \<le> F}) \<sqinter> aq\<close>
    by (simp add: fun_eq_iff)
  ultimately show ?thesis
    by (simp add: Sup_sepconjConj_framest_equiv_sepconjConj_frame)
qed

lemma guar_combine:
  \<open>(rel_liftL p \<sqinter> ar) \<squnion> (rel_liftL (p \<^emph>\<and> F) \<sqinter> ar) = rel_liftL (p \<squnion> p \<^emph>\<and> F) \<sqinter> ar\<close>
  by (simp add: inf_sup_distrib2 rel_liftL_disj_distrib)

end