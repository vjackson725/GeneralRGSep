theory RGLogic
  imports Lang
begin


definition
  \<open>cancellative' Ia Ib F \<equiv>
    \<forall>lsa lsb fs ss.
      Ia (lsa, ss) \<longrightarrow> Ib (lsb, ss) \<longrightarrow>
      F (fs, ss) \<longrightarrow>
      lsa ## fs \<longrightarrow> lsb ## fs \<longrightarrow>
      lsa + fs = lsb + fs \<longrightarrow> lsa = lsb\<close>


section \<open> Rely-Guarantee Separation Logic \<close>

inductive rgsat ::
  \<open>('l::pre_perm_alg \<times> 's) comm \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    ('l \<times> 's \<Rightarrow> bool) \<Rightarrow>
    (('l \<times> 's) comm \<Rightarrow> bool) \<Rightarrow>
    bool\<close>
  where
  rgsat_skip:
  \<open>sswa R p \<le> q \<Longrightarrow>
    sswa R p \<le> I \<Longrightarrow>
    C Skip \<Longrightarrow>
    rgsat Skip R G p q I F C\<close>
| rgsat_iter:
  \<open>rgsat c R G (sswa R i) i I F C \<Longrightarrow>
    sswa R p \<le> i \<Longrightarrow>
    sswa R i \<le> q \<Longrightarrow>
    C (Iter c) \<Longrightarrow>
    rgsat (Iter c) R G p q I F C\<close>
| rgsat_seq:
  \<open>rgsat ca r g p pp Ia F C \<Longrightarrow>
    rgsat cb r g pp q Ib F C \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    C (ca ;; cb) \<Longrightarrow>
    rgsat (ca ;; cb) r g p q I F C\<close>
| rgsat_indet:
  \<open>rgsat ca r Ga p qa Ia F C \<Longrightarrow>
    rgsat cb r Gb p qb Ib F C \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    C (ca \<^bold>\<sqinter> cb) \<Longrightarrow>
    rgsat (ca \<^bold>\<sqinter> cb) r G p q I F C\<close>
| rgsat_endet:
  \<open>rgsat ca r Ga p qa Ia F C \<Longrightarrow>
    rgsat cb r Gb p qb Ib F C \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    qa \<le> q \<Longrightarrow> qb \<le> q \<Longrightarrow>
    Ia \<le> I \<Longrightarrow> Ib \<le> I \<Longrightarrow>
    C (ca \<^bold>\<box> cb) \<Longrightarrow>
    rgsat (ca \<^bold>\<box> cb) r G p q I F C\<close>
| rgsat_par:
  \<open>rgsat ca (R \<squnion> Gb) Ga pa qa Ia (Ib \<squnion> Ib \<^emph>\<and> F) C \<Longrightarrow>
    rgsat cb (R \<squnion> Ga) Gb pb qb Ib (Ia \<squnion> Ia \<^emph>\<and> F) C \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    p \<le> pa \<^emph>\<and> pb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    C (ca \<parallel> cb) \<Longrightarrow>
    rgsat (ca \<parallel> cb) R G p q I F C\<close>
| rgsat_atom:
  \<open>p' \<le> wssa R p \<Longrightarrow>
    sswa R q \<le> q' \<Longrightarrow>
    \<comment> \<open> plain \<close>
    sp ar p \<le> q \<Longrightarrow>
    rel_liftL p \<sqinter> ar \<le> \<top> \<times>\<^sub>R G \<Longrightarrow>
    \<comment> \<open> framed \<close>
    \<forall>f\<le>F. sp ar (p \<^emph>\<and> f) \<le> q \<^emph>\<and> f \<Longrightarrow>
    rel_liftL (p \<^emph>\<and> F) \<sqinter> ar \<le> \<top> \<times>\<^sub>R G \<Longrightarrow>
    \<comment> \<open> misc \<close>
    sswa R p \<le> I \<Longrightarrow>
    sswa R q \<le> I \<Longrightarrow>
    C \<langle>ar\<rangle> \<Longrightarrow>
    rgsat \<langle>ar\<rangle> R G p' q' I F C\<close>
| rgsat_frame:
  \<open>rgsat c R G p q I (F \<^emph>\<and> F' \<squnion> F \<squnion> F') C \<Longrightarrow>
    sswa (R \<squnion> G) F' \<le> F' \<Longrightarrow>
    rgsat c R G (p \<^emph>\<and> F') (q \<^emph>\<and> F') (I \<^emph>\<and> F') F C\<close>
| rgsat_weaken:
  \<open>rgsat c r' g' p' q' I' F' C \<Longrightarrow>
    p \<le> p' \<Longrightarrow>
    q' \<le> q \<Longrightarrow>
    r \<le> r' \<Longrightarrow>
    g' \<le> g \<Longrightarrow>
    I' \<le> I \<Longrightarrow>
    F \<le> F' \<Longrightarrow>
    rgsat c r g p q I F C\<close>
| rgsat_Disj:
  \<open>p' \<le> \<Squnion>P \<Longrightarrow>
    \<forall>p\<in>P. rgsat c R G p q I F C \<Longrightarrow>
    rgsat c R G p' q I F C\<close>
| rgsat_Conj:
  \<open>\<Sqinter>\<I> \<le> I' \<Longrightarrow>
    \<Sqinter>\<G> \<le> G' \<Longrightarrow>
    \<Sqinter>Q \<le> q' \<Longrightarrow>
    \<I> \<noteq> {} \<Longrightarrow>
    \<G> \<noteq> {} \<Longrightarrow>
    Q \<noteq> {} \<Longrightarrow>
    \<forall>G\<in>\<G>. \<forall>I\<in>\<I>. \<forall>q\<in>Q. rgsat c R G p q I F C \<Longrightarrow>
    cancellative' (\<Squnion>\<I>) (\<Squnion>\<I>) (sswa (\<Squnion>\<G>) F) \<Longrightarrow>
    rgsat c R G' p q' I' F C\<close>

abbreviation rgsat_pretty
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  (\<open>_, _, _, _, _ \<turnstile> { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>r, g, L, F, C \<turnstile> { p } c { q } \<equiv> rgsat c r g p q L F C\<close>

inductive_cases rgsat_skipE[elim]: \<open>rgsat Skip R G p q I F C\<close>
inductive_cases rgsat_seqE[elim]: \<open>rgsat (c1 ;; c2) R G p q I F C\<close>
inductive_cases rgsat_iterE[elim]: \<open>rgsat (DO c OD) R G p q I F C\<close>
inductive_cases rgsat_parE[elim]: \<open>rgsat (c1 \<parallel> c2) R G p q I F C\<close>
inductive_cases rgsat_atomE[elim]: \<open>rgsat \<langle>ar\<rangle> R G p q I F C\<close>
inductive_cases rgsat_indetE[elim]: \<open>rgsat (c1 \<^bold>\<sqinter> c2) R G p q I F C\<close>
inductive_cases rgsat_endetE[elim]: \<open>rgsat (c1 \<^bold>\<box> c2) R G p q I F C\<close>


lemma rgsat_skip_forwards:
  \<open>C Skip \<Longrightarrow> rgsat Skip r g p (sswa r p) (sswa r p) F C\<close>
  by (rule rgsat_skip) force+

lemma rgsat_skip_backwards:
  \<open>C Skip \<Longrightarrow> rgsat Skip r g (wssa r q) q q F C\<close>
  by (rule rgsat_weaken[OF rgsat_skip _ _ order.refl order.refl,
        where p'=\<open>wssa r q\<close> and q'=q and I'=q and F'=F]) force+

lemma rgsat_impossible[intro]:
  \<open>rgsat c R G \<bottom> q I F C\<close>
  using rgsat_Disj[where P=\<open>{}\<close>]
  by blast

lemma rgsat_disj:
  \<open>rgsat c R G pa q I F C \<Longrightarrow>
    rgsat c R G pb q I F C \<Longrightarrow>
    rgsat c R G (pa \<squnion> pb) q I F C\<close>
  using rgsat_Disj[where P=\<open>{pa, pb}\<close>, OF order.refl]
  by simp

lemma rgsat_conj:
  \<open>rgsat c R G p qa I F C \<Longrightarrow>
    rgsat c R G p qb I F C \<Longrightarrow>
    cancellative' I I (sswa G F) \<Longrightarrow>
    rgsat c R G p (qa \<sqinter> qb) I F C\<close>
  using rgsat_Conj[of \<open>{I}\<close> I \<open>{G}\<close> G \<open>{qa, qb}\<close> \<open>qa \<sqinter> qb\<close> c R p F C]
  by (simp add: rgsat_weaken[where I=\<top>] rgsat_weaken[where g=\<top>] rgsat_weaken[where q=\<top>])

(* TODO: move *)
lemma top_relTimes_top[simp]:
  \<open>\<top> \<times>\<^sub>R \<top> = \<top>\<close>
  by fastforce

lemma rgsat_precond_implies_stateinv:
  assumes \<open>R, G, I, F, C \<turnstile> { p } c { q }\<close>
  shows \<open>sswa R p \<le> I\<close>
  using assms
proof (induct rule: rgsat.inducts)
  case (rgsat_par ca R Gb Ga pa qa Ia Ib F C cb pb qb G p q I)
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
  case (rgsat_weaken c R' G' p' q' I' F' C p q R G I F)
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
    by (meson order.trans sswa_weaker wlp_weaker_iff_sp_stronger)
qed fast+


(* TODO: not true, because of weakening *)
lemma rgsat_restrict_stateinv:
  assumes \<open>R, G, I, F, C \<turnstile> { p } c { q }\<close>
  shows \<open>R, G, wssa R I, F, C \<turnstile> { p } c { q }\<close>
  using assms
  oops

lemma rgsat_par_alt:
  \<open>rgsat ca (R \<squnion> Gb) Ga pa qa Ia (Ib \<squnion> Ib \<^emph>\<and> F) C \<Longrightarrow>
    rgsat cb (R \<squnion> Ga) Gb pb qb Ib (Ia \<squnion> Ia \<^emph>\<and> F) C \<Longrightarrow>
    Ga \<le> G \<Longrightarrow> Gb \<le> G \<Longrightarrow>
    p \<le> pa \<^emph>\<and> pb \<Longrightarrow>
    sswa (R \<squnion> Gb) qa \<^emph>\<and> sswa (R \<squnion> Ga) qb \<le> q \<Longrightarrow>
    sswa (R \<squnion> Gb) Ia \<^emph>\<and> sswa (R \<squnion> Ga) Ib \<le> I \<Longrightarrow>
    C (ca \<parallel> cb) \<Longrightarrow>
    rgsat (ca \<parallel> cb) R G p q I F C\<close>
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
  assumes \<open>R, G, I, F, C \<turnstile> { p } c { q }\<close>
  shows \<open>q \<le> I\<close>
  oops

(*
text \<open>
  The strongest weakening rule we can prove by induction.
  This is because the frame rule stabilises not just on \<open>r\<close> (antimono) but also \<open>g\<close> (mono).
  It is nevertheless sound to use the stronger version.
\<close>
lemma rgsat_weak_weaken:
  \<open>rgsat c r g p q L \<top> \<Longrightarrow>
      p' \<le> p \<Longrightarrow>
      q \<le> q' \<Longrightarrow>
      r' \<le> r \<Longrightarrow>
      L \<le> S' \<Longrightarrow>
      rgsat c r' g' p' q' S' \<top>\<close>
proof(induct arbitrary: r' g' p' q' S' rule: rgsat.inducts)
  case (rgsat_skip r p q L g F)
  then show ?case
    by (intro rgsat.rgsat_skip)
      (meson order.trans relyrel_mono sp_mono; fail)+
next
  case (rgsat_iter c r g i L F C p q)
  then show ?case
    sorry
    apply (intro rgsat.rgsat_iter[of _ _ _ i L])
       apply (metis order.refl sswa_rel_mono)
      apply (meson order.trans relyrel_mono wlp_rel_antimono; fail)
     apply (meson order.trans relyrel_mono sp_rel_mono; fail)
    apply (meson order.trans relyrel_mono sp_rel_mono; fail)
    done
next
  case (rgsat_seq c1 r g p1 p2 S1 F c2 p3 S2 L)
  then show ?case
    apply (intro rgsat.rgsat_seq[where ?S1.0=S1 and ?S2.0=S2])
      apply blast
     apply force
    apply order
    done
next
  case (rgsat_indet c1 r g1 p q1 L1 F c2 g2 q2 L2 g q L)
  
  show ?case
    using rgsat_indet.prems rgsat_indet.hyps(5-)
      rgsat.rgsat_indet[OF rgsat_indet.hyps(2) rgsat_indet.hyps(4)]
    by (meson order_refl order_trans)
next
  case (rgsat_endet c1 r g1 p q1 L1 F c2 g2 q2 L2 g q L)

  show ?case
    using rgsat_endet.prems rgsat_endet.hyps(5-)
      rgsat.rgsat_endet[OF rgsat_endet.hyps(2) rgsat_endet.hyps(4)]
    by (meson order_refl order_trans)
next
  case (rgsat_par s1 r g2 g1 p1 q1 S1 S2 F s2 p2 q2 g p q S)
  
  show ?case
    using rgsat_par.prems rgsat_par.hyps(5-)
    apply (intro rgsat.rgsat_par[OF rgsat_par.hyps(2) rgsat_par.hyps(4)])
    sorry
next
  case (rgsat_atom p' r p q q' ap F aq g L)
  then show ?case
    sorry
next
  case (rgsat_frame c r g p q L F C p' f q' F' L')
  then show ?case
    sorry
next
  case (rgsat_weaken c ra' ga' pa' qa' Sa' Fa' p q r g L F C)

  from rgsat_weaken.hyps(3-) rgsat_weaken.prems
  show ?case
    using rgsat.rgsat_weaken[of c r' g' p' q' S' Fa'] rgsat_weaken.hyps(2)
    by simp
next
  case (rgsat_Disj p' P c r g q L F C)
  then show ?case
    using rgsat.rgsat_Disj[of _ P c]
    by simp
next
  case (rgsat_Conj Q c r g p L F C q')
  then show ?case
    using rgsat.rgsat_Conj[of Q c]
    by simp
qed
    (* par *)
       apply (rule_tac ?p1.0=p1 and ?p2.0=p2 and ?q1.0=q1 and ?q2.0=q2 and ?g1.0=g1 and ?g2.0=g2
      and ?L1.0=L1 and ?L2.0=L2 and ?F1.0=F1 and ?F2.0=F2 in rgsat.rgsat_par)
              apply (meson order.refl sup_mono; fail)
             apply (meson order.refl sup_mono; fail)
            apply order
           apply order
          apply order
         apply (meson order.trans le_disj_eq_absorb relyrel_mono sepconj_conj_mono sp_mono
      sup_mono; fail)
        apply order
       apply order
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
     apply (simp; fail)
    (* frame *)
     apply (rule_tac p=p and q=q and r=ra in rgsat.rgsat_frame)
          apply blast
         apply (rule order.trans; assumption)
        apply (meson order.trans le_disj_eq_absorb sepconj_conj_monoR sswa_rel_mono sup.mono; fail)
       apply (meson order.refl order.trans sp_rel_mono relyrel_mono sup_mono; fail)
      apply (meson order.trans le_disj_eq_absorb sepimp_conj_mono sswa_rel_mono sup.mono)
     apply (simp; fail)
  done
*)


section \<open> Specialised Rules \<close>

subsection \<open> Assert \<close>

definition pred_Times_third
  :: \<open>('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('a \<times> ('b \<times> 'c) \<Rightarrow> bool)\<close>
  (infix \<open>\<times>\<^sub>P\<^sub>3\<close> 80)
  where
  \<open>p \<times>\<^sub>P\<^sub>3 q \<equiv> \<lambda>(a,(b,c)). p (a,b) \<and> q c\<close>

lemma pred_Times_third_apply[simp]:
  \<open>(p \<times>\<^sub>P\<^sub>3 q) x = (p (fst x, fst (snd x)) \<and> q (snd (snd x)))\<close>
  by (simp add: pred_Times_third_def split: prod.splits)


abbreviation
  \<open>nocrash_pred p \<equiv> p \<times>\<^sub>P\<^sub>3 (=) Running\<close>

lemmas nocrash_pred_def =
  pred_Times_third_def[of _ \<open>(=) Running\<close>]

abbreviation crash_rgsat_pretty
  (\<open>_, _, _, _, _ \<turnstile>\<^sub>k { _ } _ { _ }\<close> [55, 0, 0, 0, 0, 55, 55, 55] 56) where
  \<open>R, G, I, F, C \<turnstile>\<^sub>k { p } c { q } \<equiv>
    rgsat c
      (R \<times>\<^sub>R (=)) (G \<times>\<^sub>R (=))
      (nocrash_pred p) (nocrash_pred q)
      (nocrash_pred I) (nocrash_pred F)
      C\<close>


lemma sp_triple_relTimes_predTimes3_eq[simp]:
  \<open>sp (ra \<times>\<^sub>R (rb \<times>\<^sub>R rc)) (p \<times>\<^sub>P\<^sub>3 q) = sp (ra \<times>\<^sub>R rb) p \<times>\<^sub>P\<^sub>3 sp rc q\<close>
  by (force simp add: sp_def pred_Times_third_def)

lemma reflp_wlp_equals_predTimes3_eq[simp]:
  \<open>reflp ra \<Longrightarrow> reflp rb \<Longrightarrow>
    wlp (ra \<times>\<^sub>R rb \<times>\<^sub>R (=)) (p \<times>\<^sub>P\<^sub>3 q) = wlp (ra \<times>\<^sub>R rb) p \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: wlp_def pred_Times_third_def fun_eq_iff reflp_def)

lemma predTimes3_sepconj_conj_distrib:
  \<open>(p \<^emph>\<and> f) \<times>\<^sub>P\<^sub>3 q = p \<times>\<^sub>P\<^sub>3 q \<^emph>\<and> f \<times>\<^sub>P\<^sub>3 q\<close>
  by (force simp add: pred_Times_third_def sepconj_conj_apply fun_eq_iff)

lemma predTimes3_eqVal_le_iff[simp]:
  \<open>pa \<times>\<^sub>P\<^sub>3 (=) v \<le> pb \<times>\<^sub>P\<^sub>3 (=) v \<longleftrightarrow> pa \<le> pb\<close>
  by (force simp add: pred_Times_third_def)

lemma all_impl_nocrash_pred_internalise:
  \<open>(\<forall>p\<le>nocrash_pred P. q p) \<longleftrightarrow> (\<forall>p\<le>P. q (nocrash_pred p))\<close>
  apply (simp add: pred_Times_third_def le_fun_def)
  apply (intro iffI allI impI, force)
  apply (drule_tac x=\<open>\<lambda>(l,s). \<exists>k. p (l, s, Running)\<close> in spec)
  apply (clarsimp split: prod.splits)
  apply (subgoal_tac \<open>(\<lambda>(l, s, k). p (l, s, Running) \<and> Running = k) = p\<close>; force)
  done

lemma sp_crash_healthy_rel_eq:
  \<open>sp (crash_healthy_rel r) (nocrash_pred p) =
    (\<lambda>(l', s', k'). (\<exists>s. r s (l', s', k') \<and> p s))\<close>
  by (simp add: sp_def fun_eq_iff)

lemma rgsat_assert:
  assumes plain:
    \<open>sswa R p \<le> pa\<close>
    \<open>sswa R p \<le> q\<close>
    \<open>rel_liftL (sswa R p) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    and framed:
    \<open>sswa R p \<^emph>\<and> F \<le> pa\<close>
    \<open>\<forall>f\<le>F. sswa R p \<^emph>\<and> f \<le> q \<^emph>\<and> f\<close>
    \<open>rel_liftL (sswa R p \<^emph>\<and> F) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    and misc:
    \<open>sswa R p \<le> I\<close>
    \<open>sswa R q \<le> I\<close>
    \<open>C (Assert pa)\<close>
  shows
    \<open>R, G, I, F, C \<turnstile>\<^sub>k { p } Assert pa { q }\<close>
  using assms
  unfolding Assert_def
proof (intro rgsat_atom[where q=\<open>nocrash_pred (sswa R p)\<close>])
  let ?ra' = \<open>(crash_healthy_rel
            (\<lambda>(l, s) (l', s', k').
                l' = l \<and>
                s' = s \<and> (pa (l, s) \<and> k' = Running \<or> \<not> pa (l, s) \<and> k' = Crashed)))\<close>

  show
    \<open>sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nocrash_pred p)) \<le> (nocrash_pred (sswa R p))\<close>
    using plain
    by (force simp add: all_impl_nocrash_pred_internalise
        predTimes3_sepconj_conj_distrib[symmetric] sp_crash_healthy_rel_eq)
  show
    \<open>rel_liftL (sswa (R \<times>\<^sub>R (=)) (nocrash_pred p)) \<sqinter> ?ra' \<le> \<top> \<times>\<^sub>R G \<times>\<^sub>R (=)\<close>
    using plain
    by (force simp add: predTimes3_sepconj_conj_distrib[symmetric] le_fun_def)

  show
    \<open>\<forall>f\<le>nocrash_pred F.
       sp ?ra' (sswa (R \<times>\<^sub>R (=)) (nocrash_pred p) \<^emph>\<and> f) \<le> nocrash_pred (sswa R p) \<^emph>\<and> f\<close>
    using framed
    by (simp add: all_impl_nocrash_pred_internalise
        predTimes3_sepconj_conj_distrib[symmetric] sp_crash_healthy_rel_eq,
        fastforce simp add: le_fun_def sepconj_conj_apply)
  show
    \<open>rel_liftL (sswa (R \<times>\<^sub>R (=)) (nocrash_pred p) \<^emph>\<and> nocrash_pred F) \<sqinter> ?ra' \<le> \<top> \<times>\<^sub>R G \<times>\<^sub>R (=)\<close>
    using framed
    by (force simp add: predTimes3_sepconj_conj_distrib[symmetric] le_fun_def)
qed (simp add: sswa_weaker wssa_stronger)+


subsection \<open> Await \<close>

lemma rgsat_await:
  assumes
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> qa \<le> (sswa R p \<sqinter> qa) \<^emph>\<and> f\<close>
    \<open>rel_liftL (sswa R p \<sqinter> qa) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>rel_liftL ((sswa R p \<^emph>\<and> F) \<sqinter> qa) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>sswa R (sswa R p \<sqinter> qa) \<le> q\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>sswa R (sswa R p \<sqinter> qa) \<le> I\<close>
    \<open>C (Await qa)\<close>
  shows
    \<open>R, G, I, F, C \<turnstile> { p } Await qa { q }\<close>
  using assms
  unfolding Await_def
  apply (intro rgsat_atom[where p=\<open>sswa R p\<close> and q=\<open>sswa R p \<sqinter> qa\<close>])
          apply force
         apply (simp add: inf_assoc rel_liftL_conj_distrib; fail)+
  done

text \<open>
  Note: the rule does not attempt to prevent the Await from deadlocking for no reason.
  One should also show that the Await-predicate is achievable from the current state
  with \<open>R\<close> steps. I.e. \<open>\<exists>s. sp R\<^sup>*\<^sup>* ((sswa R p \<^emph>\<and> F) \<sqinter> qa) s\<close>
    This doesn't prevent all deadlocks, but does ensure that, if one does occur,
  some of the blame for it falls on the environment specification.
\<close>


subsection \<open> If-then-else \<close>

lemma rgsat_if_then_else:
  assumes
    \<open>rel_liftL (sswa R p) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>rel_liftL (sswa R p \<^emph>\<and> F) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    and tt_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> pp \<le> (sswa R p \<sqinter> pp) \<^emph>\<and> f\<close>
    and ff_guard_frame_cond:
    \<open>\<forall>f\<le>F. (sswa R p \<^emph>\<and> f) \<sqinter> -pp \<le> (sswa R p \<sqinter> -pp) \<^emph>\<and> f\<close> 
    and body_assms:
    \<open>R, G, Ia, F, C \<turnstile> { sswa R (sswa R p \<sqinter> pp) } ctt { qa }\<close>
    \<open>R, G, Ib, F, C \<turnstile> { sswa R (sswa R p \<sqinter> -pp) } cff { qb }\<close>
    and misc_assms:
    \<open>C (Await pp)\<close>
    \<open>C (Await (-pp))\<close>
    \<open>C (Await pp ;; ctt)\<close>
    \<open>C (Await (- pp) ;; cff)\<close>
    \<open>C (IfThenElse pp ctt cff)\<close>
    \<open>sswa R p \<le> I\<close>
    \<open>Ia \<le> I\<close>
    \<open>Ib \<le> I\<close>
    \<open>qa \<le> q\<close>
    \<open>qb \<le> q\<close>
  shows
    \<open>R, G, I, F, C \<turnstile> { p } IfThenElse pp ctt cff { q }\<close>
  using misc_assms
  unfolding IfThenElse_def
proof (intro rgsat_endet[OF rgsat_seq rgsat_seq order.refl order.refl,
      where I=I and Ia=\<open>sswa R p \<squnion> Ia\<close> and Ib=\<open>sswa R p \<squnion> Ib\<close>])
  show \<open>R, G, sswa R p, F, C \<turnstile> { p } Await pp { sswa R (sswa R p \<sqinter> pp) }\<close>
    using misc_assms assms(1-2) tt_guard_frame_cond
    apply (intro rgsat_await; simp)
      apply (meson order.eq_iff order.trans inf_mono inf_sup_ord(1) liftL_mono; fail)
     apply (meson order.eq_iff order.trans inf_mono inf_sup_ord(1) liftL_mono; fail)
    apply (meson le_infI1 relyrel_trans transp_relcompp wlp_sp_weak_absorb
        wlp_weaker_iff_sp_stronger)
    done
  show \<open>R, G, Ia, F, C \<turnstile> { sswa R (sswa R p \<sqinter> pp) } ctt { qa }\<close>
    using body_assms
    by blast
  show \<open>R, G, sswa R p, F, C \<turnstile> { p } Await (- pp) { sswa R (sswa R p \<sqinter> -pp) }\<close>
    using ff_guard_frame_cond misc_assms assms
    apply (intro rgsat_await; simp)
      apply (meson order.eq_iff order.trans inf_mono inf_sup_ord(1) liftL_mono; fail)
     apply (meson order.eq_iff order.trans inf_mono inf_sup_ord(1) liftL_mono; fail)
    apply (meson le_infI1 relyrel_trans transp_relcompp wlp_sp_weak_absorb
        wlp_weaker_iff_sp_stronger)
    done
  show \<open>R, G, Ib, F, C \<turnstile> { sswa R (sswa R p \<sqinter> -pp) } cff { qb }\<close>
    using body_assms
    by blast
  show \<open>sswa R p \<squnion> Ia \<le> I\<close>
    using misc_assms(6,7)
    by simp
  show \<open>sswa R p \<squnion> Ib \<le> I\<close>
    using misc_assms(6,8)
    by simp
qed simp+


subsection \<open> WhileLoop \<close>

lemma rgsat_while_stable:
  assumes frame_cond:
    \<open>\<forall>f\<le>F. (sswa R i \<^emph>\<and> f) \<sqinter> px \<le> (sswa R i \<sqinter> px) \<^emph>\<and> f\<close>
    and guar_conds:
    \<open>rel_liftL (sswa R i \<sqinter> px) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    \<open>rel_liftL ((sswa R i \<^emph>\<and> F) \<sqinter> px) \<sqinter> (=) \<le> \<top> \<times>\<^sub>R G\<close>
    and rgsat_body:
    \<open>R, G, I, F, C \<turnstile> { sswa R (sswa R i \<sqinter> px) } c { sswa R i }\<close>
    and misc:
    \<open>sswa R (i \<squnion> I) \<le> I'\<close>
    \<open>C (Await px)\<close>
    \<open>C (Await px ;; c)\<close>
    \<open>C (DO Await px ;; c OD)\<close>
  shows
    \<open>R, G, I', F, C \<turnstile> { i } WhileLoop px c { sswa R i }\<close>
  unfolding WhileLoop_def
  using assms
  apply -
  oops
(*
  apply (rule rgsat_iter[where i=\<open>sswa R i\<close> and I=\<open>i \<squnion> I\<close>, OF rgsat_seq[OF rgsat_await,
          where Ia=\<open>sswa R i \<squnion> sswa R (sswa R i \<sqinter> px)\<close> and Ib=I]]; simp)
   apply (meson order.trans rgsat_precond_in_localst sp_pred_mono sswa_weaker sup.cobounded2
      sup_ge1; fail)
  done
*)


subsection \<open> Atom Variants \<close>

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
    apply (clarsimp simp add: le_fun_def sepconj_conj_def, fast)
   apply (clarsimp simp add: le_fun_def sepconj_conj_def sp_def imp_conjL imp_ex_conjL; fail)
  apply (rule order.antisym; simp add: le_fun_def sepconj_conj_def imp_conjL imp_ex_conjL; metis)
  done

lemma atom_variant_compressed_frame2_nequiv:
  \<open>(sp aq (wssa r p \<^emph>\<and> F) \<le> q \<^emph>\<and> F) \<longrightarrow> (\<forall>f\<le>F. sp aq (wssa r p \<^emph>\<and> f) \<le> q \<^emph>\<and> f)\<close>
  nitpick[card 'a=1, card 'b=2]
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

lemma guar_rel_helper:
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

end